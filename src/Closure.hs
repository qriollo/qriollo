
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

module Closure(
        closureConvert, test_closureConvert, test_closedVars
    ) where 

import Control.Applicative((<$>))
import Control.Monad(mapM_, filterM, zipWithM_)
import Control.Monad.Trans.State.Lazy(
        State, get, modify, evalState, runState, execState
    )
import qualified Data.Map as Map(
        Map, empty, insert, delete, lookup, member, keys, findWithDefault,
        fromList, toList,
    )
import Data.Maybe(fromJust)
import Data.List(union, (\\), sort, intersect)
import Deps(Dependency(..), dependencySortK)
import Env(
        Env,
        envEmpty, envPushFrame, envPopFrame, envDefine, envGet,
        envIsLocallyDefined,
    )
import Optim(contractUntilNoChanges)

import ExpressionK

data ClosureState = ClosureState {
    cssNextFreshId :: Integer,

    -- Maps a function to its declaration
    cssFunctionDecl :: Map.Map IdK DeclarationK,

    -- Maps a function to the set of free variables
    -- that are referenced in the body of the function
    -- and that are *not* let-bound.
    cssFunctionFreevars :: Map.Map IdK [IdK],

    -- Bound variables, used for collecting available variables
    cssBound :: Map.Map IdK (),

    -- Maps a function to the set of variables that
    -- are available at the point where this function is defined.
    cssAvailableVars :: Map.Map IdK [IdK],

    -- Tells if an identifier is used in escaping position,
    -- i.e. other than as the head of an application.
    --
    -- Note that identifiers which are not bound to functions
    -- by a LetK are still considered escaping even if they do
    -- not belong to this dictionary.
    cssEscaping :: Map.Map IdK (),

    -- Maps a function to the set of all variables that
    -- should be included in the closure
    cssFunctionClosureVars :: Map.Map IdK [IdK],

    -- Maps each closure function to two fresh identifiers.
    cssCompanionVars :: Map.Map IdK (IdK, IdK),

    -- The closure conversion procedure renames some
    -- variables to particular values.
    cssRename :: Env IdK ValueK,

    -- Functions that must use the "known" calling convention.
    -- Remaining functions are represented with closures.
    cssUseKnownCallingConvention :: Map.Map IdK () 
  }

type ClosureM = State ClosureState

unionMap :: Eq b => (a -> [b]) -> [a] -> [b]
unionMap f = foldr union [] . map f

unionMapM :: (Eq b, Monad m) => (a -> m [b]) -> [a] -> m [b]
unionMapM f xs = do
  xss <- mapM f xs
  return $ foldr union [] xss

declId :: DeclarationK -> IdK
declId (ValueDK x _ _) = x

freeVarsV :: ValueK -> [IdK]
freeVarsV (VarK x) = [x]
freeVarsV _ = []

freeVars :: ExprK -> [IdK]
freeVars (RecordK vals id expr) =
  unionMap freeVarsV vals `union` (freeVars expr \\ [id])
freeVars (SelectK _ val id expr) =
  freeVarsV val `union` (freeVars expr \\ [id])
freeVars (AppK val vals) =
  freeVarsV val `union` unionMap freeVarsV vals
freeVars (LetK decls expr) =
   (unionMap freeVarsDecl decls `union` freeVars expr) \\ map declId decls
 where
   freeVarsDecl :: DeclarationK -> [IdK]
   freeVarsDecl (ValueDK _ params body) = freeVars body \\ params
freeVars (SwitchK val exprs) =
  freeVarsV val `union` unionMap freeVars exprs
freeVars (PrimitiveK _ vals ids exprs) =
  unionMap freeVarsV vals `union` (unionMap freeVars exprs \\ ids)
freeVars (ForeignK _ vals id expr) =
  unionMap freeVarsV vals `union` (freeVars expr \\ [id])

calledFunctions :: ExprK -> [IdK]
calledFunctions (RecordK _ _ expr)       = calledFunctions expr
calledFunctions (SelectK _ _ _ expr)     = calledFunctions expr
calledFunctions (AppK val vals)          = freeVarsV val
calledFunctions (LetK decls expr)        =
    unionMap calledFunctionsDecl decls `union` calledFunctions expr
  where
    calledFunctionsDecl :: DeclarationK -> [IdK]
    calledFunctionsDecl (ValueDK _ _ expr) = calledFunctions expr
calledFunctions (SwitchK _ exprs)        = unionMap calledFunctions exprs
calledFunctions (PrimitiveK _ _ _ exprs) = unionMap calledFunctions exprs
calledFunctions (ForeignK _ _ _ expr)    = calledFunctions expr

test_closureConvert :: ExprK -> ExprK
test_closureConvert expr =
  evalState (closureConvertExpr expr) (initialState expr)

closureConvert :: ExprK -> ExprK
closureConvert expr =
  let expr' = evalState (closureConvertExpr expr) (initialState expr) in
    flattenExpression . contractUntilNoChanges $ expr'

initialState :: ExprK -> ClosureState
initialState expr =
   ClosureState {
     cssNextFreshId = maximum (allIds expr) + 1,
     cssFunctionDecl = Map.fromList [
       -- Toplevel continuation
       (-1, ValueDK (-1) [] $ AppK (VarK (-1)) [])
     ],
     cssBound = Map.empty,
     cssAvailableVars = Map.empty,
     cssFunctionFreevars = Map.fromList [
       -- Toplevel continuation has no free vars
       (-1, [])
     ],
     cssEscaping = Map.empty,
     cssFunctionClosureVars = Map.empty,
     cssCompanionVars = Map.empty,
     cssRename = envEmpty,
     cssUseKnownCallingConvention = Map.fromList [
       -- Toplevel continuation is known
       (-1, ())
     ]
   }

-- Calculate the variables that must be closed for each definition.
-- (Used only for testing).
test_closedVars :: ExprK -> [(IdK, [IdK])]
test_closedVars expr =
    let state = execState (calcClosedVars expr) (initialState expr) in
      map (\ (f, vs) -> (f, sort vs)) $
      Map.toList (cssFunctionClosureVars state)
  where
    calcClosedVars :: ExprK -> ClosureM ()
    calcClosedVars expr = do
      collect expr
      postCollect expr
      calculateClosureOfFreevars

closureConvertExpr :: ExprK -> ClosureM ExprK
closureConvertExpr expr = do
    let expr' = sortDependencies expr in do
      -- Collect function declarations, free variables
      -- and escaping information
      collect expr'
      postCollect expr'

      -- Calculate the variables that must be closed by each
      -- function definition.
      calculateClosureOfFreevars

      -- Convert all functions 
      convert expr'
  where
    sortDependencies :: ExprK -> ExprK
    sortDependencies (RecordK vals id expr) =
      RecordK vals id (sortDependencies expr)
    sortDependencies (SelectK n val id expr) =
      SelectK n val id (sortDependencies expr)
    sortDependencies (AppK val vals) =
      AppK val vals
    sortDependencies (LetK decls expr) =
        foldr (\ (DpFunctions decls) ->
                 LetK (map sortDependenciesDecl decls))
              (sortDependencies expr)
              (dependencySortK decls)
      where
        sortDependenciesDecl :: DeclarationK -> DeclarationK
        sortDependenciesDecl (ValueDK x ids expr) =
          ValueDK x ids (sortDependencies expr)
    sortDependencies (SwitchK val exprs) =
      SwitchK val (map sortDependencies exprs)
    sortDependencies (PrimitiveK p vals ids exprs) =
      PrimitiveK p vals ids (map sortDependencies exprs)
    sortDependencies (ForeignK sig vals id expr) =
      ForeignK sig vals id (sortDependencies expr)

    convertVar :: IdK -> ClosureM ValueK
    convertVar x = do
      state <- get
      case envGet x (cssRename state) of
        Nothing -> return $ VarK x
        Just v  ->
          if envIsLocallyDefined x (cssRename state)
           then return v
           else error ("(closureConvert: La variable " ++ show x ++
                       " no está definida localmente)")

    convertV :: ValueK -> ClosureM ValueK
    convertV (VarK x) = convertVar x
    convertV v        = return v

    freshIdK :: ClosureM IdK
    freshIdK = do
      state <- get
      modify (\ state -> state { cssNextFreshId = cssNextFreshId state + 1 })
      return $ cssNextFreshId state

    -- Let func be a function with free variables x1 ... xN.
    --
    -- A known function declaration
    --   ValueDK func params body
    -- is translated to
    --   ValueDK func (params ++ [y1, ..., yN])
    --       body{x1 := y1, ..., xN := yN}
    --
    -- A known function call
    --   AppK func args
    -- is translated to
    --   AppK func (args ++ [x1, ... xN])
    --
    -- Escaping function declarations
    --   ValueDK func params body
    -- are translated to
    --
    --   ValueDK funcCode (params + [funcData])
    --     body{func := #0(funcData),
    --          x1 := #1(funcData), ..., xN := #N(funcData)}
    --
    -- plus a record allocation (the "closure" itself):
    --
    --   RecordK [funcCode, x1, ... xN] func
    --
    -- An escaping function call
    --   AppK func args
    -- is translated to
    --   AppK #0(func) (args ++ [func])
    --
    convert :: ExprK -> ClosureM ExprK
    convert (RecordK vals id expr) = do
      vals' <- mapM convertV vals
      RecordK vals' id <$> convert expr
    convert (SelectK n val id expr) = do
      val' <- convertV val
      SelectK n val' id <$> convert expr
    convert (AppK val vals) = do
      known <- usesKnownCallingConventionV val
      if known
       then do
         vals' <- mapM convertV vals
         let VarK f = val in do
           fvs   <- functionClosureVars f
           fvs'  <- mapM convertVar fvs
           return $ AppK val (vals' ++ fvs')
       else do
         val'  <- convertV val
         vals' <- mapM convertV vals
         valCode <- freshIdK
         return $ SelectK 0 val' valCode
                    (AppK (VarK valCode) (vals' ++ [val']))
    convert (LetK decls expr) = do
        convertDecls decls expr
      where
        convertDecls :: [DeclarationK] -> ExprK -> ClosureM ExprK
        convertDecls [decl@(ValueDK func _ _)] expr = do
          known <- usesKnownCallingConvention func
          if known
           then convertKnownDecl decl expr
           else convertClosureDecls [decl] expr
        convertDecls decls expr = do
          convertClosureDecls decls expr

        convertKnownDecl :: DeclarationK -> ExprK -> ClosureM ExprK
        convertKnownDecl (ValueDK func params body) expr = do
          fvs <- functionClosureVars func
          freshIds <- mapM (const freshIdK) fvs
          pushRenameFrame
          zipWithM_ defineRename fvs (map VarK freshIds)
          body' <- convert body
          popRenameFrame
          expr' <- convert expr
          return (
            LetK [ValueDK func (params ++ freshIds) body']
                 expr'
           )

        convertClosureDecls :: [DeclarationK] -> ExprK -> ClosureM ExprK
        convertClosureDecls decls expr = do
          fvs <- unionMapM functionClosureVars (map declId decls)
          mapM_ declareCompanionVars decls
          decls' <- mapM (convertClosureDecl fvs decls) decls
          fvs' <- mapM convertVar fvs
          expr' <- convert expr
          return $
            LetK decls' $
              foldr (\ (func, funcCode) ->
                       RecordK (VarK funcCode : fvs') func)
                    expr'
                    (zip (map declId decls)
                         (map declId decls'))

        convertClosureDecl :: [IdK] -> [DeclarationK] ->
                              DeclarationK -> ClosureM DeclarationK
        convertClosureDecl fvs decls (ValueDK func params body) = do
          (funcCode, funcData) <- companionVars func
          freshIds  <- mapM (const freshIdK) fvs
          pushRenameFrame
          defineRename func (VarK funcData)

          let siblings = map declId decls \\ [func]
           in do
             siblingClosures <-
                  mapM (makeClosureForSibling freshIds)
                       siblings
             zipWithM_ defineRename fvs (map VarK freshIds)
             body' <- convert body
             popRenameFrame
             return (
               ValueDK funcCode (params ++ [funcData]) $
                 foldr (\ (freshId, i) ->
                            SelectK i (VarK funcData) freshId)
                       (foldr ($) body' siblingClosures)
                       (zip freshIds [1..])
              )

        makeClosureForSibling :: [IdK] -> IdK -> ClosureM (ExprK -> ExprK)
        makeClosureForSibling freshIds sibling = do
          (siblingCode, _) <- companionVars sibling
          siblingDataFresh <- freshIdK
          defineRename sibling (VarK siblingDataFresh)
          return (
            RecordK (VarK siblingCode : map VarK freshIds)
                    siblingDataFresh
           )

        declareCompanionVars :: DeclarationK -> ClosureM ()
        declareCompanionVars (ValueDK func _ _) = do
          funcCode <- freshIdK
          funcData <- freshIdK
          modify (\ state -> state {
            cssCompanionVars = Map.insert func (funcCode, funcData)
                                          (cssCompanionVars state)
          })

        companionVars :: IdK -> ClosureM (IdK, IdK)
        companionVars func = do
          state <- get
          return $ Map.findWithDefault (error "") func
                                       (cssCompanionVars state)

    convert (SwitchK val exprs) = do
      val' <- convertV val
      SwitchK val' <$> mapM convert exprs
    convert (PrimitiveK p vals ids exprs) = do
      vals' <- mapM convertV vals
      PrimitiveK p vals' ids <$> mapM convert exprs
    convert (ForeignK sig vals id expr) = do
      vals' <- mapM convertV vals
      ForeignK sig vals' id <$> convert expr

    pushRenameFrame :: ClosureM ()
    pushRenameFrame = modify (\ state -> state {
      cssRename = envPushFrame (cssRename state)
    })

    defineRename :: IdK -> ValueK -> ClosureM ()
    defineRename x v = do
      known <- usesKnownCallingConvention x
      if known
       then error "(closureConvert: se redefine una función conocida)"
       else return ()
      modify (\ state -> state {
        cssRename = envDefine x v (cssRename state)
      })

    popRenameFrame :: ClosureM ()
    popRenameFrame = modify (\ state -> state {
      cssRename = envPopFrame (cssRename state)
    })

    functionClosureVars :: IdK -> ClosureM [IdK]
    functionClosureVars f = do
      state <- get
      case Map.lookup f (cssFunctionClosureVars state) of
        Just x  -> return x
        Nothing -> error "(closureConvert: la función no es conocida)"

getFunctionDecl :: IdK -> ClosureM DeclarationK
getFunctionDecl func = do
  state <- get
  return $ Map.findWithDefault
             (error "(closureConversion: no es una función)")
             func (cssFunctionDecl state)

getFunctionClosureVars :: IdK -> ClosureM [IdK]
getFunctionClosureVars func = do
  state <- get
  return $ Map.findWithDefault [] func (cssFunctionClosureVars state)

escape :: IdK -> ClosureM ()
escape x = modify (\ state -> state {
  cssEscaping = Map.insert x () (cssEscaping state)
})

escapeVal :: ValueK -> ClosureM ()
escapeVal (VarK x) = escape x
escapeVal _        = return ()

bind :: IdK -> ClosureM ()
bind x = modify (\ state -> state {
  cssBound = Map.insert x () (cssBound state)
})

unbind :: IdK -> ClosureM ()
unbind x = modify (\ state -> state {
  cssBound = Map.delete x (cssBound state)
})

-- Detect escaping vs. known functions
collect :: ExprK -> ClosureM ()
collect (RecordK vals id expr) = do
  mapM_ escapeVal vals
  collect expr
collect (SelectK _ val id expr) = do
  escapeVal val
  collect expr
collect (AppK val vals) = do
  -- Note: val does not escape
  mapM_ escapeVal vals
collect (LetK decls expr) = do 
    mapM_ collectDecl decls
    collect expr
    case decls of
      [ValueDK func _ _] -> do
          escapes <- isEscaping func
          if escapes
           then return ()
           else modify (\ state -> state {
                  cssUseKnownCallingConvention =
                    Map.insert func () (cssUseKnownCallingConvention state)
                })
      _ -> return ()
  where
    collectDecl :: DeclarationK -> ClosureM ()
    collectDecl decl@(ValueDK f _ body) = do
      modify (\ state -> state {
        cssFunctionDecl =
          Map.insert f decl (cssFunctionDecl state)
      })
      collect body
collect (SwitchK val exprs) = do
  escapeVal val
  mapM_ collect exprs
collect (PrimitiveK _ vals ids exprs) = do
  mapM_ escapeVal vals
  mapM_ collect exprs
collect (ForeignK _ vals id expr) = do
  mapM_ escapeVal vals
  collect expr

-- Collect declarations, free and available vars for each
-- function. Depends on `collect' to know whether functions
-- are escaping or known.
postCollect :: ExprK -> ClosureM ()
postCollect (RecordK vals id expr) = do
  bind id
  postCollect expr
  unbind id
postCollect (SelectK _ val id expr) = do
  bind id
  postCollect expr
  unbind id
postCollect (AppK val vals) = return ()
postCollect (LetK decls expr) = do 
    mapM_ bind (map declId decls)
    mapM_ postCollectDecl decls
    postCollect expr
    mapM_ unbind (map declId decls)
  where
    postCollectDecl :: DeclarationK -> ClosureM ()
    postCollectDecl (ValueDK f params body) = do
      mapM_ bind params
      postCollect body
      mapM_ unbind params
      state <- get
      let boundForF = params `union`
                      map declId decls `union`
                      Map.keys (cssUseKnownCallingConvention state)
       in do
         modify (\ state -> state {
           cssFunctionFreevars =
             Map.insert f
                        (freeVars body \\ boundForF)
                        (cssFunctionFreevars state),
           cssAvailableVars =
             Map.insert f
                        (Map.keys (cssBound state) \\ map declId decls)
                        (cssAvailableVars state)
         })
postCollect (SwitchK val exprs) = do
  mapM_ postCollect exprs
postCollect (PrimitiveK _ vals ids exprs) = do
  mapM_ bind ids
  mapM_ postCollect exprs
  mapM_ unbind ids
postCollect (ForeignK _ vals id expr) = do
  bind id
  postCollect expr
  unbind id

isEscaping :: IdK -> ClosureM Bool
isEscaping x = do
  state <- get
  case Map.lookup x (cssFunctionDecl state) of
    Just _  -> return $ Map.member x (cssEscaping state)
    Nothing -> return True

usesKnownCallingConvention :: IdK -> ClosureM Bool
usesKnownCallingConvention x = do
  state <- get
  return $ Map.member x (cssUseKnownCallingConvention state)

usesKnownCallingConventionV :: ValueK -> ClosureM Bool
usesKnownCallingConventionV (VarK x) = usesKnownCallingConvention x
usesKnownCallingConventionV _        = return False

calculateClosureOfFreevars :: ClosureM ()
calculateClosureOfFreevars = do
    init
    findFixpoint
    intersectWithAvailable
  where
    -- The closure of the free variables is initialized
    -- with the set of free variables.
    init :: ClosureM ()
    init = modify (\ state -> state {
      cssFunctionClosureVars = cssFunctionFreevars state
    })

    findFixpoint :: ClosureM ()
    findFixpoint = do
      state <- get
      change <- propagate (Map.keys (cssFunctionDecl state))
      if change
       then findFixpoint
       else return ()

    intersectWithAvailable :: ClosureM ()
    intersectWithAvailable = do
        state <- get
        mapM_ intersectClosureVars (Map.keys (cssFunctionDecl state))
      where
        intersectClosureVars :: IdK -> ClosureM ()
        intersectClosureVars func = do
          state <- get
          let closureVars  = Map.findWithDefault
                               (error "") func
                               (cssFunctionClosureVars state)
              available    = Map.findWithDefault
                               (error "") func
                               (cssAvailableVars state)
              closureVars' = closureVars `intersect` available
           in modify (\ state -> state {
               cssFunctionClosureVars =
                 Map.insert func closureVars'
                            (cssFunctionClosureVars state)
              })

    -- Propagate free variables to the callers.
    -- Return True if there is any change.
    propagate :: [IdK] -> ClosureM Bool
    propagate [] = return False
    propagate (func : funcs) = do
      b <- propagate funcs
      oldClv <- getFunctionClosureVars func
      newClv <- candidateClosureVars func
      if all (\ v -> v `elem` oldClv) newClv
       then return b   -- No change here
       else do
         -- Change
         modify (\ state -> state {
           cssFunctionClosureVars =
             Map.insert func
                        (oldClv `union` newClv)
                        (cssFunctionClosureVars state)
         })
         return True

    candidateClosureVars :: IdK -> ClosureM [IdK]
    candidateClosureVars func = do
      ValueDK _ params body <- getFunctionDecl func
      let called = calledFunctions body in do
        knownCalled <- filterM usesKnownCallingConvention called
        clv <- unionMapM getFunctionClosureVars knownCalled
        return clv

type FlatState = Map.Map IdK DeclarationK
type FlatM = State FlatState

flattenExpression :: ExprK -> ExprK
flattenExpression expr =
    let (expr', state) = runState (flat expr) Map.empty in
      LetK (map snd (Map.toList state)) expr'
  where
    flat :: ExprK -> FlatM ExprK
    flat (RecordK vals id expr) = do
      vals' <- mapM flatV vals
      RecordK vals' id <$> flat expr
    flat (SelectK n val id expr) = do
      val' <- flatV val
      SelectK n val' id <$> flat expr
    flat (AppK val vals) = do
      val'  <- flatV val
      vals' <- mapM flatV vals
      return $ AppK val' vals'
    flat (LetK decls expr) = do
        mapM_ declareFunc decls
        mapM_ flatDecl decls
        flat expr
      where
        declareFunc :: DeclarationK -> FlatM ()
        declareFunc (ValueDK x _ _) = do
          modify (Map.insert x (error ""))
        flatDecl :: DeclarationK -> FlatM ()
        flatDecl (ValueDK x params expr) = do
          expr' <- flat expr
          modify (Map.insert x (ValueDK x params expr'))
    flat (SwitchK val exprs) = do
      val' <- flatV val
      SwitchK val' <$> mapM flat exprs
    flat (PrimitiveK p vals ids exprs) = do
      vals' <- mapM flatV vals
      PrimitiveK p vals' ids <$> mapM flat exprs
    flat (ForeignK sig vals id expr) = do
      vals' <- mapM flatV vals
      ForeignK sig vals' id <$> flat expr

    flatV :: ValueK -> FlatM ValueK
    flatV (VarK (-1)) = return $ LabelK (-1) -- Toplevel continuation
    flatV (VarK x) = do
      state <- get
      case Map.lookup x state of
        Nothing -> return $ VarK x
        Just _  -> return $ LabelK x
    flatV v = return v

