
-- Este archivo es parte de Qriollo.

-- Qriollo is free software: you can redistribute it and/or modify
-- it under the terms of the GNU General Public License as published by
-- the Free Software Foundation, either version 3 of the License, or
-- (at your option) any later version.
--
-- Qriollo is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.
--
-- You should have received a copy of the GNU General Public License
-- along with Qriollo.  If not, see <http://www.gnu.org/licenses/>.

module Optim(
        optimizeExpr, OptimOptions(..), OptimInfo(..),
        contractUntilNoChanges,

        -- For testing
        betaContract, deadCodeElim, etaContract, betaExpand,
    ) where

import qualified Data.Map as Map(
        Map, empty, member, lookup, insert, findWithDefault, fromList,
    )
 
import Control.Applicative((<$>))
import Control.Monad(zipWithM, zipWithM_)
import Control.Monad.Trans.State.Lazy(State, get, modify, runState, evalState)

import ExpressionE
import ExpressionL
import ExpressionK
import Primitive(primMinFixnum, primMaxFixnum)
import qualified Eval

data OptimOptions = OptimizeForSpace
                  | OptimizeForTime

data OptimInfo a = OptimInfo {
                      osChanges :: Integer,
                      osResult :: a
                   }

inc :: Ord a => a -> Map.Map a Integer -> Map.Map a Integer
inc key dict = Map.insert key (Map.findWithDefault 0 key dict + 1) dict

addElem :: Ord a => a -> b -> Map.Map a [b] -> Map.Map a [b]
addElem key elem dict =
    Map.insert key (elem : Map.findWithDefault [] key dict) dict

optimizeExpr :: OptimOptions -> Integer -> ExprK -> ExprK
optimizeExpr options 0       expr = expr
optimizeExpr options nRounds expr = rec nRounds expr
  where
    rec :: Integer -> ExprK -> ExprK
    rec 0 expr = contractUntilNoChanges expr
    rec n expr = contractUntilNoChanges .
                 osResult . betaExpand options n .
                 osResult . etaContract .
                 rec (n - 1) $
                 expr

contractUntilNoChanges :: ExprK -> ExprK
contractUntilNoChanges expr =
  let OptimInfo changes1 expr'  = betaContract expr
      OptimInfo changes2 expr'' = deadCodeElim expr'
   in
    if changes1 + changes2 < changeThreshold
     then expr''
     else contractUntilNoChanges expr''
  where
    changeThreshold :: Integer
    changeThreshold = 5

----

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = do
  xss <- mapM f xs
  return $ concat xss

---- Beta contraction phase

-- - Inlining of functions used exactly once.
-- - Dead variable elimination:
--     - Erase unused let-bound variables.
--     - Erase unused record creations.
--     - Erase unused selections.
--     - Erase unused primitives as long as they have no side-effects.
-- - Constant folding of switches when the index is known.
-- - Constant folding of selects when the record is known.
-- - Constant folding of primitive operations,
--   including the branching operations.
-- - Erase unused arguments of known functions.
--   A function is said to be "known" when is is used exclusively
--   in head position (it is not an argument; i.e. it does not escape).

data BetaConState = BetaConState {

    --- Collected information about an expression

    -- Declaration of a function.
    bcsFunctionDecls :: Map.Map IdK DeclarationK,

    -- Known record declarations.
    bcsRecordDecls :: Map.Map IdK [ValueK],

    -- Number of times a variable is used.
    bcsUses :: Map.Map IdK Integer,

    -- Number of times a variable is used other than in
    -- the head of an application.
    bcsEscapes :: Map.Map IdK Integer,

    -- Number of times a function is used as a function
    -- *after* the point of its definition.
    bcsFunctionUses :: Map.Map IdK Integer,

    --- Dynamic state kept to beta-contract

    -- If x is defined, replace (VarK x) by its value here.
    -- Used for constant folding.
    bcsReplacement :: Map.Map IdK ValueK,

    bcsChanges :: Integer
  }

type BetaConM = State BetaConState

hasSideEffects :: Primop -> Bool
hasSideEffects PrimRef       = False
hasSideEffects PrimDeref     = False
hasSideEffects PrimAssign    = True
hasSideEffects PrimFixnumAdd = False
hasSideEffects PrimFixnumSub = False
hasSideEffects PrimFixnumEq  = False
hasSideEffects PrimFixnumLe  = False
hasSideEffects PrimBoxed     = False
hasSideEffects PrimTag       = False
hasSideEffects PrimPutChar   = True
--
hasSideEffects PrimFixnumMul    = False
hasSideEffects PrimFixnumDiv    = True  -- zero division
hasSideEffects PrimFixnumMod    = True  -- zero division
hasSideEffects PrimFixnumNe     = False
hasSideEffects PrimFixnumLt     = False
hasSideEffects PrimFixnumGe     = False
hasSideEffects PrimFixnumGt     = False
hasSideEffects PrimFixnumLshift = False
hasSideEffects PrimFixnumRshift = False
hasSideEffects PrimFixnumOrb    = False
hasSideEffects PrimFixnumAndb   = False
hasSideEffects PrimFixnumXorb   = False
hasSideEffects PrimFixnumNotb   = False
--
hasSideEffects PrimCharOrd      = False
hasSideEffects PrimCharChr      = False
hasSideEffects PrimSystemExit   = True
--
hasSideEffects PrimContinuationCallCC = True
hasSideEffects PrimContinuationThrow  = True

alphaEquivalent :: ExprK -> ExprK -> Bool
alphaEquivalent expr1 expr2 =
    evalState (rec expr1 expr2) Map.empty
  where
    rec :: ExprK -> ExprK -> State (Map.Map IdK IdK) Bool
    rec (RecordK vals1 id1 expr1)
        (RecordK vals2 id2 expr2) = do
      vals1' <- mapM translateVal vals1
      assignId id1 id2
      b      <- rec expr1 expr2
      return (vals1' == vals2 && b)
    rec (SelectK n1 val1 id1 expr1)
        (SelectK n2 val2 id2 expr2) = do
      val1' <- translateVal val1
      assignId id1 id2
      b     <- rec expr1 expr2
      return (n1 == n2 &&
              val1' == val2 &&
              b)
    rec (AppK val1 vals1)
        (AppK val2 vals2) = do
      val1' <- translateVal val1
      vals1' <- mapM translateVal vals1
      return (val1' == val2 && vals1' == vals2)
    rec (LetK decls1 expr1)
        (LetK decls2 expr2) = do
      zipWithM_ assignId (concatMap declIds decls1)
                         (concatMap declIds decls2)
      recBodies <- zipWithM rec (map declBody decls1)
                                (map declBody decls2)
      b <- rec expr1 expr2
      return (
        length decls1 == length decls2 &&
        all (\ (d1, d2) ->
               length (declIds d1) == length (declIds d2))
            (zip decls1 decls2) &&
        and recBodies &&
        b
       )
    rec (SwitchK val1 exprs1)
        (SwitchK val2 exprs2) = do
      val1' <- translateVal val1
      recExprs <- zipWithM rec exprs1 exprs2
      return (val1' == val2 &&
              length exprs1 == length exprs2 &&
              and recExprs)
    rec (PrimitiveK primop1 vals1 ids1 exprs1)
        (PrimitiveK primop2 vals2 ids2 exprs2) = do
      vals1' <- mapM translateVal vals1
      zipWithM_ assignId ids1 ids2
      recExprs <- zipWithM rec exprs1 exprs2
      return (primop1 == primop2 &&
              vals1' == vals2 &&
              length exprs1 == length exprs2 &&
              and recExprs)
    rec (ForeignK sig1 vals1 id1 expr1)
        (ForeignK sig2 vals2 id2 expr2) = do
      vals1' <- mapM translateVal vals1
      assignId id1 id2
      b <- rec expr1 expr2
      return (sig1 == sig2 &&
              vals1' == vals2 &&
              b)
    rec _ _ = return False

    declIds :: DeclarationK -> [IdK]
    declIds (ValueDK x ps _) = x : ps

    declBody :: DeclarationK -> ExprK
    declBody (ValueDK _ _ body) = body

    assignId :: IdK -> IdK -> State (Map.Map IdK IdK) ()
    assignId id1 id2 = modify (Map.insert id1 id2)

    translateVal :: ValueK -> State (Map.Map IdK IdK) ValueK
    translateVal (VarK x)      = do
      x' <- translateId x
      return $ VarK x'
    translateVal (ConstantK c) = return $ ConstantK c

    translateId :: IdK -> State (Map.Map IdK IdK) IdK
    translateId x = do
      dict <- get
      case Map.lookup x dict of
        Nothing -> return x
        Just y  -> return y

betaContract :: ExprK -> OptimInfo ExprK
betaContract expr =
    let (expr', state) = runState (betaContractExpr expr) initialState
     in OptimInfo {
          osChanges = bcsChanges state,
          osResult  = expr'
        }
  where
    initialState :: BetaConState
    initialState = BetaConState {
                     bcsFunctionDecls = Map.empty,
                     bcsRecordDecls = Map.empty,
                     bcsUses = Map.empty,
                     bcsEscapes = Map.empty,
                     bcsFunctionUses = Map.empty,
                     bcsReplacement = Map.empty,
                     bcsChanges = 0
                   }

    betaContractExpr :: ExprK -> BetaConM ExprK
    betaContractExpr expr = do
      collect expr
      contract expr

    click :: BetaConM ()
    click = do
      modify (\ state -> state { bcsChanges = bcsChanges state + 1 })

    setReplacement :: IdK -> ValueK -> BetaConM ()
    setReplacement id val = do
      state <- get
      case Map.lookup id (bcsReplacement state) of
        Nothing -> return ()
        Just _  ->
          error "(betaContract: conflicto de reemplazos para la variable)"
      modify (\ state -> state {
        bcsReplacement = Map.insert id val (bcsReplacement state)
      })

    useValue :: ValueK -> BetaConM ()
    useValue (VarK x) = do
      modify (\ state -> state {
        bcsUses = inc x (bcsUses state)
      })
    useValue _ = return ()

    varEscapes :: ValueK -> BetaConM ()
    varEscapes (VarK x) = do
      modify (\ state -> state {
        bcsEscapes = inc x (bcsEscapes state)
      })
    varEscapes _ = return ()

    useFunction :: ValueK -> Integer -> BetaConM ()
    useFunction (VarK f) arity = do
      state <- get
      case Map.lookup f (bcsFunctionDecls state) of
        Nothing -> return ()
        Just (ValueDK _ params body)
          | fromIntegral (length params) /= arity ->
              error "(betaContract: expresión deforme; difieren las aridades)"
          | otherwise ->
              modify (\ state -> state {
                bcsFunctionUses = inc f (bcsFunctionUses state)
              })
    useFunction _ _ = return ()

    collect :: ExprK -> BetaConM ()
    collect (RecordK vals id expr) = do
      modify (\ state -> state {
        bcsRecordDecls = Map.insert id vals (bcsRecordDecls state)
      })
      mapM_ useValue vals
      mapM_ varEscapes vals
      collect expr
    collect (SelectK n val id expr) = do
      useValue val
      varEscapes val
      collect expr
    collect (AppK val vals) = do
      useValue val -- Does not escape
      useFunction val (fromIntegral (length vals))
      mapM_ useValue vals
      mapM_ varEscapes vals
    collect (LetK decls expr) = do
        mapM_ defineFunction decls
        collect expr
      where
        defineFunction :: DeclarationK -> BetaConM ()
        defineFunction decl@(ValueDK x _ body) = do
          collect body
          -- Declare the function only after analyzing its body
          -- to avoid beta-contracting occurrences of the function
          -- on its own body.
          modify (\ state -> state {
            bcsFunctionDecls = Map.insert x decl (bcsFunctionDecls state)
          })
    collect (SwitchK val exprs) = do
      useValue val
      varEscapes val
      mapM_ collect exprs
    collect (PrimitiveK _ vals _ exprs) = do
      mapM_ useValue vals
      mapM_ varEscapes vals
      mapM_ collect exprs
    collect (ForeignK _ vals _ expr) = do
      mapM_ useValue vals
      mapM_ varEscapes vals
      collect expr

    replaceVal :: ValueK -> BetaConM ValueK
    replaceVal (VarK id) = do
      state <- get
      case Map.lookup id (bcsReplacement state) of
        Nothing  -> return (VarK id)
        Just val -> return val
    replaceVal val = return val

    contract :: ExprK -> BetaConM ExprK
    contract (RecordK vals id expr) = do
      b <- canErase id
      if b
       then do
         click
         contract expr
       else do
         vals' <- mapM replaceVal vals
         RecordK vals' id <$> contract expr
    contract (SelectK n val id expr) = do
      b <- canErase id
      if b
       then do
         click
         contract expr
       else do
         val' <- replaceVal val
         mRecord <- recordDeclarationFor val'
         case mRecord of
           Just values | 0 <= n && n < fromIntegral (length values) ->
             do click
                val'' <- replaceVal (values !! fromIntegral n)
                setReplacement id val''
                contract expr
           _ -> SelectK n val' id <$> contract expr
    contract (AppK val vals) = do
      val' <- replaceVal val
      vals' <- mapM replaceVal vals
      case val' of
        VarK var -> do
          known <- functionIsKnown var -- Does not escape
          vals'' <- keepUsedArguments var vals'

          b <- shouldContract var
          if b
           then do
             ValueDK _ args body <- functionDeclarationFor var
             args' <- keepUsedArguments var args
             zipWithM_ setReplacement args' vals''
             contract body
           else return $ AppK (VarK var) vals''
        _ -> return $ AppK val' vals'
    contract (LetK decls body) = do
      declsList <- mapM contractDecl decls
      body' <- contract body
      let decls' = concat declsList in
        if null decls'
         then return body'
         else return $ LetK decls' body'
    contract (SwitchK val exprs) = do
      val' <- replaceVal val
      case val' of
        ConstantK (FixnumC i)
          | 0 <= i && i < fromIntegral (length exprs) ->
             do
               click
               contract (exprs !! fromIntegral i)
        _ -> do
                exprs' <- mapM contract exprs
                return $ SwitchK val' exprs'
    contract prim@(PrimitiveK _ _ _ _) =
      contractPrimitive prim
    contract (ForeignK sig vals id expr) = do
      vals' <- mapM replaceVal vals
      expr' <- contract expr
      return $ ForeignK sig vals' id expr'

    contractDecl :: DeclarationK -> BetaConM [DeclarationK]
    contractDecl (ValueDK f args body) = do
      b <- shouldContractOrErase f
      if b 
       then do
         click
         return []
       else do
         body' <- contract body

         known <- functionIsKnown f -- Does not escape
         args' <- keepUsedArguments f args

         return [ValueDK f args' body']

    contractPrimitive :: ExprK -> BetaConM ExprK
    contractPrimitive prim@(PrimitiveK primop vals [id] [expr])
      | not (hasSideEffects primop) = do
          b <- canErase id
          if b
            then do
                   click
                   contract expr
            else do
                   vals' <- mapM replaceVal vals
                   constantFoldPrimitive primop vals' [id] [expr]
    contractPrimitive (PrimitiveK primop vals ids exprs) = do
      vals' <- mapM replaceVal vals
      constantFoldPrimitive primop vals' ids exprs

    -- Constant folding
    constantFoldPrimitive :: Primop -> [ValueK] -> [IdK] -> [ExprK] ->
                             BetaConM ExprK
    constantFoldPrimitive PrimFixnumAdd [
                            ConstantK (FixnumC n),
                            ConstantK (FixnumC m)
                          ] [result] [expr] = do
      click
      setReplacement result (ConstantK $ FixnumC (Eval.fixnumAdd n m))
      contract expr
    constantFoldPrimitive PrimFixnumAdd [
                            ConstantK (FixnumC 0),
                            val
                          ] [result] [expr] = do
      click
      val' <- replaceVal val
      setReplacement result val'
      contract expr
    constantFoldPrimitive PrimFixnumAdd [
                            val,
                            ConstantK (FixnumC 0)
                          ] [result] [expr] = do
      click
      val' <- replaceVal val
      setReplacement result val'
      contract expr
    constantFoldPrimitive PrimFixnumSub [
                            ConstantK (FixnumC n),
                            ConstantK (FixnumC m)
                          ] [result] [expr] = do
      click
      setReplacement result (ConstantK $ FixnumC (Eval.fixnumSub n m))
      contract expr
    constantFoldPrimitive PrimFixnumSub [
                            val,
                            ConstantK (FixnumC 0)
                          ] [result] [expr] = do
      click
      val' <- replaceVal val
      setReplacement result val'
      contract expr
    constantFoldPrimitive PrimFixnumEq [
                            ConstantK (FixnumC n),
                            ConstantK (FixnumC m)
                          ] [] [expr1, expr2] = do
      click
      if n == m
       then contract expr1
       else contract expr2
    constantFoldPrimitive PrimFixnumEq [_, _] [] [expr1, expr2]
      | alphaEquivalent expr1 expr2 = do
          click
          contract expr1
    constantFoldPrimitive PrimFixnumLe [
                            ConstantK (FixnumC n),
                            ConstantK (FixnumC m)
                          ] [] [expr1, expr2] = do
      click
      if n <= m
       then contract expr1
       else contract expr2
    constantFoldPrimitive PrimFixnumLe [
                            ConstantK (FixnumC n),
                            _
                          ] [] [expr1, _]
      | n == primMinFixnum = do
        click
        contract expr1
    constantFoldPrimitive PrimFixnumLe [
                            _,
                            ConstantK (FixnumC n)
                          ] [] [_, expr2]
      | n == primMaxFixnum = do
        click
        contract expr2
    constantFoldPrimitive PrimFixnumLe [_, _] [] [expr1, expr2]
      | alphaEquivalent expr1 expr2 = do
          click
          contract expr1
    -- Delete redundant comparisons introduced by the match compiler
    constantFoldPrimitive PrimFixnumLe [v1, v2] [] [
                            PrimitiveK PrimFixnumLe [w1, w2] [] [expr1, expr2],
                            expr3
                          ]
      | v1 == w1 && v2 == w2 = do
          click
          constantFoldPrimitive PrimFixnumLe [v1, v2] [] [expr1, expr3]
    -- For effect and value => for effect
    constantFoldPrimitive PrimPutChar [val] [ret] [expr] = do
        val'  <- replaceVal val
        expr' <- contract expr
        b <- canErase ret
        if b
         then do
           click
           return $ PrimitiveK PrimPutChar [val'] [] [expr']
         else do
           return $ PrimitiveK PrimPutChar [val'] [ret] [expr']
    -- For effect and value => for effect
    constantFoldPrimitive PrimAssign [vref, vval] [ret] [expr] = do
        vref' <- replaceVal vref
        vval' <- replaceVal vval
        expr' <- contract expr
        b <- canErase ret
        if b
         then do
           click
           return $ PrimitiveK PrimAssign [vref', vval'] [] [expr']
         else do
           return $ PrimitiveK PrimAssign [vref', vval'] [ret] [expr']
    constantFoldPrimitive PrimBoxed [val] [] [expr1, expr2] = do
      val' <- replaceVal val
      case val' of
        ConstantK _ -> do
          -- Constants are unboxed
          click
          contract expr2
        _ -> do
          mRecord <- recordDeclarationFor val'
          case mRecord of
            Just _  -> do
              -- Records are boxed
              click
              contract expr1
            _ -> do
              -- Otherwise proceed with normal compilation
              expr1' <- contract expr1
              expr2' <- contract expr2
              return $ PrimitiveK PrimBoxed [val'] [] [expr1', expr2']
    constantFoldPrimitive PrimTag [val] [result] [expr] = do
      val' <- replaceVal val
      case val' of
        ConstantK c -> do
          -- Evaluate the tag of a constant
          click
          setReplacement result (ConstantK $ FixnumC $ Eval.constantTag c)
          contract expr
        _ -> do
          mRecord <- recordDeclarationFor val'
          case mRecord of
            Just (val : vals) -> do
              -- The tag of a record is always on its first component
              click
              setReplacement result val
              contract expr
            _ -> do
              -- Otherwise proceed with normal compilation
              expr' <- contract expr
              return $ PrimitiveK PrimTag [val'] [result] [expr']
    constantFoldPrimitive primop vals ids exprs = do
      exprs' <- mapM contract exprs
      return $ PrimitiveK primop vals ids exprs'

    shouldContract :: IdK -> BetaConM Bool
    shouldContract func = do
      state <- get
      let uses = Map.findWithDefault 0 func (bcsUses state)
          fuses = Map.findWithDefault 0 func (bcsFunctionUses state)
       in return (uses == 1 && fuses == 1)

    canErase :: IdK -> BetaConM Bool
    canErase id = do
      state <- get
      let uses = Map.findWithDefault 0 id (bcsUses state)
       in return (uses == 0)

    shouldContractOrErase :: IdK -> BetaConM Bool
    shouldContractOrErase func = do
      b1 <- shouldContract func
      b2 <- canErase func
      return (b1 || b2)

    functionDeclarationFor :: IdK -> BetaConM DeclarationK
    functionDeclarationFor func = do
      state <- get
      return $ Map.findWithDefault
                 (error "(betaContract: función no definida)")
                 func (bcsFunctionDecls state)

    recordDeclarationFor :: ValueK -> BetaConM (Maybe [ValueK])
    recordDeclarationFor (VarK rec) = do
      state <- get
      return $ Map.lookup rec (bcsRecordDecls state)
    recordDeclarationFor _ = return Nothing

    -- A function is known if it does not escape
    functionIsKnown :: IdK -> BetaConM Bool
    functionIsKnown func = do
      state <- get
      let escapes = Map.findWithDefault 0 func (bcsEscapes state)
       in return (
            Map.member func (bcsFunctionDecls state) &&
            escapes == 0)

    keepUsedArguments :: IdK -> [a] -> BetaConM [a]
    keepUsedArguments func args = do
        known <- functionIsKnown func -- Does not escape
        if known
          then do
            state <- get
            case Map.lookup func (bcsFunctionDecls state) of
              Nothing ->
                error "(betaContract: debería ser una función conocida)"
              Just (ValueDK _ params _) -> do
                eraseMask <- mapM canErase params
                return $ map snd $ filter (not . fst) $ zip eraseMask args
          else return args

---- Dead code elimination

-- - Remove all unreachable definitions.

data DeadCodeElimState = DeadCodeElimState {
    dcsFunctionDecls :: Map.Map IdK DeclarationK,
    dcsReachable :: Map.Map IdK (),

    dcsChanges :: Integer
  }

type DeadCodeElimM = State DeadCodeElimState

deadCodeElim :: ExprK -> OptimInfo ExprK
deadCodeElim expr =
    let (expr', state) = runState (deadCodeElimExpr expr) initialState
     in OptimInfo {
          osChanges = dcsChanges state,
          osResult  = expr'
        }
  where
    initialState :: DeadCodeElimState
    initialState = DeadCodeElimState {
                     dcsFunctionDecls = Map.empty,
                     dcsReachable = Map.empty,
                     dcsChanges = 0
                   }

    click :: DeadCodeElimM ()
    click = do
      modify (\ state -> state { dcsChanges = dcsChanges state + 1 })

    deadCodeElimExpr :: ExprK -> DeadCodeElimM ExprK
    deadCodeElimExpr expr = do
      visitExpr expr
      clean expr

    isReachable :: IdK -> DeadCodeElimM Bool
    isReachable x = do
      state <- get
      return $ Map.member x (dcsReachable state)

    markAsReachable :: IdK -> DeadCodeElimM ()
    markAsReachable x =
      modify (\ state -> state {
        dcsReachable = Map.insert x () (dcsReachable state)
      })

    visit :: IdK -> DeadCodeElimM ()
    visit x = do
      state <- get
      case Map.lookup x (dcsFunctionDecls state) of
        Just (ValueDK _ args expr) -> do
          b <- isReachable x
          if b
           then return ()
           else do
             markAsReachable x
             visitExpr expr
        Nothing -> return ()

    visitValue :: ValueK -> DeadCodeElimM ()
    visitValue (VarK x) = visit x
    visitValue _ = return ()

    visitExpr :: ExprK -> DeadCodeElimM ()
    visitExpr (RecordK vals _ expr) = do
      mapM_ visitValue vals
      visitExpr expr
    visitExpr (SelectK _ val _ expr) = do
      visitValue val
      visitExpr expr
    visitExpr (AppK val vals) = do
      visitValue val
      mapM_ visitValue vals
    visitExpr (LetK decls expr) = do
        mapM_ declareFunc decls
        visitExpr expr
      where
        declareFunc :: DeclarationK -> DeadCodeElimM ()
        declareFunc decl@(ValueDK f _ _) =
          modify (\ state -> state {
            dcsFunctionDecls = Map.insert f decl (dcsFunctionDecls state)
          })
    visitExpr (SwitchK val exprs) = do
      visitValue val
      mapM_ visitExpr exprs
    visitExpr (PrimitiveK _ vals _ exprs) = do
      mapM_ visitValue vals
      mapM_ visitExpr exprs
    visitExpr (ForeignK _ vals _ expr) = do
      mapM_ visitValue vals
      visitExpr expr

    clean :: ExprK -> DeadCodeElimM ExprK
    clean (RecordK vals id expr) = RecordK vals id <$> clean expr
    clean (SelectK n val id expr) = SelectK n val id <$> clean expr
    clean (AppK val vals) = return $ AppK val vals
    clean (LetK decls expr) = do
        decls' <- concatMapM cleanDecl decls
        if null decls'
         then clean expr
         else LetK decls' <$> clean expr
      where
        cleanDecl :: DeclarationK -> DeadCodeElimM [DeclarationK]
        cleanDecl (ValueDK f args expr) = do
          b <- isReachable f
          if b
           then do
             expr' <- clean expr
             return [ValueDK f args expr']
           else do
             click
             return []
    clean (SwitchK val exprs) =
      SwitchK val <$> mapM clean exprs
    clean (PrimitiveK p vals id exprs) =
      PrimitiveK p vals id <$> mapM clean exprs
    clean (ForeignK sig vals id expr) =
      ForeignK sig vals id <$> clean expr
   
---- Eta contraction and uncurrying

-- - Eta contract declarations "f x1 ... xn = g x1 ... xn"
--   replacing f by g.
-- - Perform the uncurry transform.

data EtaConState = EtaConState {
    ecsNextFreshId :: Integer,
    ecsReplacement :: Map.Map IdK IdK,

    ecsChanges :: Integer
  }

type EtaConM = State EtaConState

etaContract :: ExprK -> OptimInfo ExprK
etaContract expr =
    let (expr', state) = runState (etaContractExpr expr) initialState
     in OptimInfo {
          osChanges = ecsChanges state,
          osResult  = expr'
        }
  where
    initialState :: EtaConState
    initialState = EtaConState {
                     ecsNextFreshId = maximum (allIds expr) + 1,
                     ecsReplacement = Map.empty,
                     ecsChanges = 0
                   }

    click :: EtaConM ()
    click = do
      modify (\ state -> state { ecsChanges = ecsChanges state + 1 })

    freshIdK :: EtaConM IdK
    freshIdK = do
      state <- get
      modify (\ state -> state { ecsNextFreshId = ecsNextFreshId state + 1 })
      return $ ecsNextFreshId state

    setReplacement :: IdK -> IdK -> EtaConM ()
    setReplacement f g =
      modify (\ state -> state {
        ecsReplacement = Map.insert f g (ecsReplacement state)
      })

    etaContractV :: ValueK -> EtaConM ValueK
    etaContractV (VarK f) = do
      state <- get
      case Map.lookup f (ecsReplacement state) of
        Just g  -> do
          click
          VarK g' <- etaContractV $ VarK g
          setReplacement f g'
          return $ VarK g'
        Nothing -> return $ VarK f
    etaContractV val = return val

    etaContractExpr :: ExprK -> EtaConM ExprK
    etaContractExpr (RecordK vals id expr) = do
        vals' <- mapM etaContractV vals
        RecordK vals' id <$> etaContractExpr expr
    etaContractExpr (SelectK n val id expr) = do
        val' <- etaContractV val
        SelectK n val' id <$> etaContractExpr expr
    etaContractExpr (AppK val vals) = do
        val'  <- etaContractV val
        vals' <- mapM etaContractV vals
        return $ AppK val' vals'
    etaContractExpr (LetK decls expr) = do
        mapM_ visitDecl decls
        decls'  <- concatMapM etaContractDecl decls
        decls'' <- concatMapM uncurryDecl decls'
        expr'   <- etaContractExpr expr
        return $ LetK decls'' expr'
      where
        visitDecl :: DeclarationK -> EtaConM ()
        visitDecl (ValueDK f1 args1 (AppK (VarK f2) args2))
          | map VarK args1 == args2 &&
            f2 /= (-1)  -- Do not eta-expand the toplevel continuation
          = do
            state <- get
            case Map.lookup f2 (ecsReplacement state) of
              Just f2' -> if f1 /= f2'
                           then setReplacement f1 f2'
                           else return ()
              Nothing  -> if f1 /= f2
                           then setReplacement f1 f2
                           else return ()
        visitDecl _ = return ()

        etaContractDecl :: DeclarationK -> EtaConM [DeclarationK]
        etaContractDecl (ValueDK f args expr) = do
          state <- get
          case Map.lookup f (ecsReplacement state) of
            Nothing -> do
              expr' <- etaContractExpr expr
              return [ValueDK f args expr']
            -- Definitions that are eta-expanded dissapear
            Just _ -> return []
    etaContractExpr (SwitchK val exprs) = do
      val' <- etaContractV val
      SwitchK val' <$> mapM etaContractExpr exprs
    etaContractExpr (PrimitiveK primop vals id exprs) = do
      vals' <- mapM etaContractV vals
      PrimitiveK primop vals' id <$> mapM etaContractExpr exprs
    etaContractExpr (ForeignK sig vals id expr) = do
      vals' <- mapM etaContractV vals
      ForeignK sig vals' id <$> etaContractExpr expr

    uncurryDecl :: DeclarationK -> EtaConM [DeclarationK]
    uncurryDecl (ValueDK f (fCont : fArgs)
                           (LetK [ValueDK g [gCont, gArg] gBody]
                                 (AppK (VarK x) [VarK y])))
      | x == fCont && y == g &&
        not (alreadyUncurried (b fCont fArgs g gCont gArg) gBody) = do
          click
          u      <- freshIdK
          fCont' <- freshIdK
          fArgs' <- mapM (const freshIdK) fArgs
          g'     <- freshIdK
          gCont' <- freshIdK
          gArg'  <- freshIdK
          return [
            ValueDK f (fCont' : fArgs')
              (LetK [ValueDK g' [gCont', gArg']
                        (AppK (VarK u)
                              (map VarK (b fCont' fArgs' g' gCont' gArg')))]
                (AppK (VarK fCont') [VarK g'])),
            ValueDK u (b fCont fArgs g gCont gArg) gBody
            ]
      where
        b :: IdK -> [IdK] -> IdK -> IdK -> IdK -> [IdK]
        b fCont fArgs g gCont gArg = [fCont] ++ fArgs ++ [g, gCont, gArg]
    uncurryDecl decl = return [decl]

    alreadyUncurried :: [IdK] -> ExprK -> Bool
    alreadyUncurried args1 (AppK _ args2) = map VarK args1 == args2
    alreadyUncurried _     _              = False

---- Beta expansion

-- Inlining of functions following a few heuristics.

data BetaExpState = BetaExpState {
    besOptions :: OptimOptions,

    -- Current round of optimization (should be read-only).
    besRound :: Integer,

    -- Current depth (nesting level of expansions).
    besDepth :: Integer,

    besNextFreshId :: Integer,

    -- Declaration of a function
    besFunctionDecls :: Map.Map IdK DeclarationK,

    -- Declaration of a record
    besRecordDecls :: Map.Map IdK [ValueK],

    -- Number of times an identifier escapes,
    -- i.e. it is used in a non-destructuring fashion:
    -- - not as the head of an application
    -- - not as the argument of a select
    besEscapingUses :: Map.Map IdK Integer,

    -- Number of times that each identifier is used in
    -- a destructuring position, i.e. it is the argument to some
    -- kind of destructor.
    -- Includes the number of times an identifier is used at the
    -- head of an application.
    besDestructuringUses :: Map.Map IdK Integer,

    -- List of all the switches taken depending on the value
    -- of the identifier.
    besSwitchingUses :: Map.Map IdK [[ExprK]],

    -- List of all the arithmetic branchings taken depending
    -- on the value of the identifier.
    besArithBranchingUses :: Map.Map IdK [[ExprK]],

    besChanges :: Integer
  }

type BetaExpM = State BetaExpState

betaExpand :: OptimOptions -> Integer -> ExprK -> OptimInfo ExprK
betaExpand options currentRound expr =
  let (expr', state) = runState (betaExpandExpr expr) initialState
   in OptimInfo {
        osChanges = besChanges state,
        osResult  = expr'
      }
  where
    initialState :: BetaExpState
    initialState = BetaExpState {
                     besOptions = options,
                     besRound = currentRound,
                     besDepth = 0,
                     besNextFreshId = maximum (allIds expr) + 1,
                     besFunctionDecls = Map.empty,
                     besRecordDecls = Map.empty,
                     besEscapingUses = Map.empty,
                     besDestructuringUses = Map.empty,
                     besSwitchingUses = Map.empty,
                     besArithBranchingUses = Map.empty,
                     besChanges = 0
                   }

    modifyDepth :: (Integer -> Integer) -> BetaExpM ()
    modifyDepth f = modify (\ state ->
      state { besDepth = f (besDepth state) })

    betaExpandExpr :: ExprK -> BetaExpM ExprK
    betaExpandExpr expr = do
      collect expr
      expand expr

    freshIdK :: BetaExpM IdK
    freshIdK = do
      state <- get
      modify (\ state -> state { besNextFreshId = besNextFreshId state + 1 })
      return $ besNextFreshId state

    escape :: IdK -> BetaExpM ()
    escape x = modify (\ state ->
      state {
        besEscapingUses = inc x (besEscapingUses state)
      })

    defineFunction :: IdK -> DeclarationK -> BetaExpM ()
    defineFunction x decl =
          modify (\ state -> state {
            besFunctionDecls = Map.insert x decl (besFunctionDecls state)
          })

    defineRecord :: IdK -> [ValueK] -> BetaExpM ()
    defineRecord x decl =
          modify (\ state -> state {
            besRecordDecls = Map.insert x decl (besRecordDecls state)
          })

    useDestructively :: IdK -> BetaExpM ()
    useDestructively x = modify (\ state ->
      state {
        besDestructuringUses = inc x (besDestructuringUses state)
      })

    switchOn :: IdK -> [ExprK] -> BetaExpM ()
    switchOn x branches = modify (\ state ->
      state {
        besSwitchingUses = addElem x branches (besSwitchingUses state)
      })

    arithBranchOn :: IdK -> [ExprK] -> BetaExpM ()
    arithBranchOn x branches = modify (\ state ->
      state {
        besArithBranchingUses = addElem x branches (besArithBranchingUses state)
      })

    escapeV :: ValueK -> BetaExpM ()
    escapeV (VarK x) = escape x
    escapeV _        = return ()

    useDestructivelyV :: ValueK -> BetaExpM ()
    useDestructivelyV (VarK x) = useDestructively x
    useDestructivelyV _        = return ()

    switchOnV :: ValueK -> [ExprK] -> BetaExpM ()
    switchOnV (VarK x) branches = switchOn x branches
    switchOnV _        _        = return ()

    collect :: ExprK -> BetaExpM ()
    collect (RecordK vals id expr) = do
      mapM_ escapeV vals
      defineRecord id vals
      collect expr
    collect (SelectK _ val id expr) = do
      -- Note: val does not escape
      useDestructivelyV val
      collect expr
    collect (AppK val vals) = do
      -- Note: val does not escape
      useDestructivelyV val
      mapM_ escapeV vals
    collect (LetK decls expr) = do
        mapM_ collectDecl decls
        collect expr
      where
        collectDecl :: DeclarationK -> BetaExpM ()
        collectDecl decl@(ValueDK f _ expr) = do
          defineFunction f decl
          collect expr
    collect (SwitchK val exprs) = do
      switchOnV val exprs
      useDestructivelyV val
      escapeV val
      mapM_ collect exprs
    collect (PrimitiveK p vals _ exprs) = do
        if isDestructive p
         then mapM_ useDestructivelyV vals
         else return ()
        mapM_ escapeV vals
        mapM_ collect exprs
        mapM_ (flip arithBranchOn exprs)
              (arithBranchings p vals)
      where
        isDestructive :: Primop -> Bool
        isDestructive PrimTag   = True
        isDestructive PrimBoxed = True
        isDestructive _         = False

        arithBranchings :: Primop -> [ValueK] -> [IdK]
        arithBranchings PrimFixnumEq [ConstantK _, VarK x] = [x]
        arithBranchings PrimFixnumEq [VarK x, ConstantK _] = [x]
        arithBranchings PrimFixnumLe [ConstantK _, VarK x] = [x]
        arithBranchings PrimFixnumLe [VarK x, ConstantK _] = [x]
        arithBranchings _ _                                = []

    collect (ForeignK _ vals _ expr) = do
      mapM_ escapeV vals
      collect expr

    click :: BetaExpM ()
    click = do
      modify (\ state -> state { besChanges = besChanges state + 1 })

    -- Beta-expand function calls.
    -- The only interesting case is AppK.
    expand :: ExprK -> BetaExpM ExprK
    expand (RecordK vals id expr) =
      RecordK vals id <$> expand expr
    expand (SelectK n val id expr) =
      SelectK n val id <$> expand expr
    expand (AppK (VarK f) vals) = do
      b <- shouldExpandApplication f vals
      if b
       then do
         click
         expandApplication f vals
       else return $ AppK (VarK f) vals
    expand (AppK val vals) =
      return $ AppK val vals
    expand (LetK decls expr) = do
        decls' <- mapM expandDecl decls
        expr' <- expand expr
        return $ LetK decls' expr'
      where
        expandDecl :: DeclarationK -> BetaExpM DeclarationK
        expandDecl (ValueDK f args expr) =
          ValueDK f args <$> expand expr
    expand (SwitchK val exprs) =
      SwitchK val <$> mapM expand exprs
    expand (PrimitiveK p vals ids exprs) =
      PrimitiveK p vals ids <$> mapM expand exprs
    expand (ForeignK sig val id expr) =
      ForeignK sig val id <$> expand expr

    -- Actual beta-expansion.
    -- Replace the function application by the body,
    -- substituting the formal parameters by the actual arguments.
    expandApplication :: IdK -> [ValueK] -> BetaExpM ExprK
    expandApplication f args = do
      state <- get
      let ValueDK _ params body =
            Map.findWithDefault (error "") f (besFunctionDecls state)
        in do
          body' <- rename (Map.fromList (zip params args)) body
          modifyDepth (+1)
          body'' <- expand body'
          modifyDepth (subtract 1)
          return body''

    extend :: IdK -> ValueK -> Map.Map IdK ValueK -> Map.Map IdK ValueK
    extend x val d =
      case Map.lookup x d of
        Just v  -> error "(betaExpand: variable ya ligada, invariante roto)"
        Nothing -> Map.insert x val d

    extends :: [(IdK, ValueK)] -> Map.Map IdK ValueK -> Map.Map IdK ValueK
    extends vs d = foldr (uncurry extend) d vs

    renameV :: Map.Map IdK ValueK -> ValueK -> ValueK
    renameV d (VarK x) =
      case Map.lookup x d of
        Just v  -> v
        Nothing -> VarK x -- unbound variable
    renameV d val = val

    -- Rename all bound identifiers to fresh ones
    rename :: Map.Map IdK ValueK -> ExprK -> BetaExpM ExprK
    rename d (RecordK vals id expr) =
      let vals' = map (renameV d) vals in do
        id' <- freshIdK
        expr' <- rename (extend id (VarK id') d) expr
        return $ RecordK vals' id' expr'
    rename d (SelectK n val id expr) =
      let val' = renameV d val in do
        id' <- freshIdK
        expr' <- rename (extend id (VarK id') d) expr
        return $ SelectK n val' id' expr'
    rename d (AppK val vals) =
      return $ AppK (renameV d val) (map (renameV d) vals)
    rename d (LetK decls expr) =
        let ids = map declId decls in do
          freshIds <- mapM (const freshIdK) ids
          let d' = extends (zip ids $ map VarK freshIds) d in do
            decls' <- zipWithM (renameDecl d') freshIds decls
            expr'  <- rename d' expr
            return $ LetK decls' expr'
      where
        declId :: DeclarationK -> IdK
        declId (ValueDK x _ _) = x

        renameDecl :: Map.Map IdK ValueK -> IdK -> DeclarationK ->
                      BetaExpM DeclarationK
        renameDecl d x' (ValueDK _ args expr) = do
          freshArgs <- mapM (const freshIdK) args
          let d' = extends (zip args $ map VarK freshArgs) d in
            ValueDK x' freshArgs <$> rename d' expr
    rename d (SwitchK val exprs) =
      let val' = renameV d val in
        SwitchK val' <$> mapM (rename d) exprs
    rename d (PrimitiveK p vals ids exprs) =
      let vals' = map (renameV d) vals in do
        freshIds <- mapM (const freshIdK) ids
        let d' = extends (zip ids $ map VarK freshIds) d in
          PrimitiveK p vals' freshIds <$> mapM (rename d') exprs
    rename d (ForeignK sig vals id expr) =
      let vals' = map (renameV d) vals in do
        id' <- freshIdK
        exprs' <- rename (extend id (VarK id') d) expr
        return $ ForeignK sig vals' id' exprs'

    -- Determine if the application of the function to the 
    -- given actual arguments should be expanded.
    -- This is a heuristic.
    shouldExpandApplication :: IdK -> [ValueK] -> BetaExpM Bool
    shouldExpandApplication f args = do
        state <- get
        case Map.lookup f (besFunctionDecls state) of
          Just decl -> shouldExpand decl
          Nothing   -> return False
      where
        shouldExpand :: DeclarationK -> BetaExpM Bool
        shouldExpand (ValueDK _ params body) =
          let costOfBody = evaluationCost body
              costOfCall = evaluationCost (AppK (VarK f) args)
           in do
            state <- get
            if besRound state * besDepth state > maxDepth
             then return False -- Avoid runaway expansion
             else do
               savings <- estimatedSavings params args
               numCalls <-
                 case Map.lookup f (besDestructuringUses state) of
                   Just n  -> return n
                   Nothing -> return 0
               costLimit <- currentCostLimit
               return (
                  fromIntegral costOfBody
                  - fromIntegral costOfCall
                  - fromIntegral savings
                  - (if numCalls > 1
                      then dq costOfBody numCalls
                      else 0)
                  + fromIntegral (besRound state * besDepth state) * costOfDepth
                  < fromIntegral costLimit
                 )
          where
            dq :: Integer -> Integer -> Double
            dq n 0 = fromIntegral 0
            dq n m = (fromIntegral n :: Double) / (fromIntegral m :: Double)
            maxDepth :: Integer
            maxDepth = 32

            -- A lower value optimizes space and yields a potentially
            -- smaller/slower program.
            -- A greater value optimizes time and yields a potentially
            -- larger/faster program.
            currentCostLimit :: BetaExpM Integer
            currentCostLimit = do
              state <- get
              case besOptions state of
                OptimizeForSpace -> return (-20)
                OptimizeForTime  -> return 20
            costOfDepth :: Double
            costOfDepth = 0.5

    length' :: [a] -> Integer
    length' = fromIntegral . length

    -- Estimate the cost of evaluating an expression
    evaluationCost :: ExprK -> Integer
    evaluationCost (RecordK vals _ expr) =
      length' vals + 2 + evaluationCost expr 
    evaluationCost (SelectK _ _ _ expr) = 1 + evaluationCost expr
    evaluationCost (AppK _ vals) = 1 + length' vals
    evaluationCost (LetK decls expr) =
        sum (map declCost decls) + evaluationCost expr
      where
        declCost :: DeclarationK -> Integer
        declCost (ValueDK _ _ expr) = 1 + evaluationCost expr
    evaluationCost (SwitchK _ exprs) =
      4 + sum (map evaluationCost exprs) + length' exprs
    evaluationCost (PrimitiveK _ vals ids exprs) =
      length' vals + length' ids + sum (map evaluationCost exprs)
    evaluationCost (ForeignK _ vals id expr) =
      2 * length' vals + 2 + evaluationCost expr

    -- Estimate the savings obtained by pairing the given
    -- formal paramenters and the given actual arguments.
    estimatedSavings :: [IdK] -> [ValueK] -> BetaExpM Integer
    estimatedSavings params args = do
        s <- zipWithM savings params args
        return $ sum s
      where
        savings :: IdK -> ValueK -> BetaExpM Integer
        savings param arg = do
          s <- mapM (\ f -> f param arg) savingFuncs
          return $ sum s

        savingFuncs :: [IdK -> ValueK -> BetaExpM Integer]
        savingFuncs = [
            svFuncEscape,
            svSelect,
            svRecordEscape,
            svFixnumSwitch,
            svFixnumArithBranching
          ]

        svFuncEscape :: IdK -> ValueK -> BetaExpM Integer
        svFuncEscape p (VarK f) = do
            funcF <- isFunction f
            escF <- nEscapingUses f
            escP <- nEscapingUses p
            if funcF && escF == 1 && escP == 0
             then return 6
             else return 0
        svFuncEscape _ _ = return 0

        svSelect :: IdK -> ValueK -> BetaExpM Integer
        svSelect p (VarK a) = do
            recA <- isRecord a
            if recA
             then nDestructuringUses p
             else return 0
        svSelect _ _ = return 0

        svRecordEscape :: IdK -> ValueK -> BetaExpM Integer
        svRecordEscape p (VarK a) = do
            recA <- isRecord a
            escA <- nEscapingUses a
            escP <- nEscapingUses p
            if recA && escA == 1 && escP == 0
             then do fieldsA <- nFields a
                     return (2 + fieldsA)
             else return 0
        svRecordEscape _ _ = return 0

        svFixnumSwitch :: IdK -> ValueK -> BetaExpM Integer
        svFixnumSwitch p (ConstantK (FixnumC _)) = do
            state <- get
            case Map.lookup p (besSwitchingUses state) of
              Just branchList -> return (sum $ map (branchSavings 4) branchList)
              Nothing         -> return 0
        svFixnumSwitch _ _ = return 0

        svFixnumArithBranching :: IdK -> ValueK -> BetaExpM Integer
        svFixnumArithBranching p (ConstantK (FixnumC _)) = do
            state <- get
            case Map.lookup p (besArithBranchingUses state) of
              Just branchList -> return (sum $ map (branchSavings 2) branchList)
              Nothing         -> return 0
        svFixnumArithBranching _ _ = return 0

        branchSavings :: Integer -> [ExprK] -> Integer
        branchSavings k []       = 0
        branchSavings k [_]      = k
        branchSavings k branches =
            k + (n * sum (map evaluationCost branches)) `div` (n - 1)
          where n = length' branches

        isFunction :: IdK -> BetaExpM Bool
        isFunction x = do
          state <- get
          case Map.lookup x (besFunctionDecls state) of
            Just _  -> return True
            Nothing -> return False

        isRecord :: IdK -> BetaExpM Bool
        isRecord x = do
          state <- get
          case Map.lookup x (besRecordDecls state) of
            Just _  -> return True
            Nothing -> return False

        nEscapingUses :: IdK -> BetaExpM Integer
        nEscapingUses x = do
          state <- get
          case Map.lookup x (besEscapingUses state) of
            Just n  -> return n
            Nothing -> return 0

        nFields :: IdK -> BetaExpM Integer
        nFields x = do
          state <- get
          case Map.lookup x (besRecordDecls state) of
            Just fields -> return $ length' fields
            Nothing     -> return 0

        nDestructuringUses :: IdK -> BetaExpM Integer
        nDestructuringUses x = do
          state <- get
          case Map.lookup x (besDestructuringUses state) of
            Just n  -> return n
            Nothing -> return 0

