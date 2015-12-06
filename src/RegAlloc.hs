
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

module RegAlloc(allocateRegisters, assignRegisters) where

import Control.Applicative((<$>))
import Control.Monad(zipWithM_)
import Control.Monad.Trans.State.Lazy(
        State, get, modify, runState, evalState
    )
import Data.List(union, intersect, (\\), sortBy, elemIndex, elemIndices)
import Data.Ord(comparing)
import qualified Data.Map as Map(
    Map, empty, lookup, insert, delete, fromList, toList, unionWith,
    member, map, findWithDefault,
  )

import ExpressionE
import ExpressionK

-- Put a bound on the number of formal/real parameters to function
-- definitions and applications, by passing the exceeding arguments
-- in a record.

data BoundParamState =
  BoundParamState {
    bpsNextFreshId :: IdK
  }

type BoundParamM = State BoundParamState

length' :: [a] -> Integer
length' = fromIntegral . length

unionMapM :: (Eq b, Monad m) => (a -> m [b]) -> [a] -> m [b]
unionMapM f xs = do
  xss <- mapM f xs
  return $ foldr union [] xss

-- Return an equivalent expression whose functions
-- take at most (n0 - 1) parameters.
boundParams :: Integer -> ExprK -> ExprK
boundParams n0 expr = evalState (bound expr) initialState
  where
    n :: Integer
    n = n0 - 1

    initialState :: BoundParamState
    initialState =
      BoundParamState {
        bpsNextFreshId = maximum (allIds expr) + 1
      }
    bound :: ExprK -> BoundParamM ExprK
    bound (RecordK vals id expr) =
      RecordK vals id <$> bound expr
    bound (SelectK i val id expr) =
      SelectK i val id <$> bound expr
    bound (AppK val vals)
      | length' vals <= n = return $ AppK val vals
      | otherwise =
        let (vals1, vals2) = splitAt (fromIntegral (n - 1)) vals in do
          r <- boundFreshIdK
          return $ RecordK vals2 r $
                   AppK val (vals1 ++ [VarK r])
    bound (LetK decls expr) = do
        decls' <- mapM boundDecl decls
        expr' <- bound expr
        return $ LetK decls' expr'
      where
        boundDecl :: DeclarationK -> BoundParamM DeclarationK
        boundDecl (ValueDK f vars body)
          | length' vars <= n =
            ValueDK f vars <$> bound body
          | otherwise =
            let (vars1, vars2) = splitAt (fromIntegral (n - 1)) vars in do
              r <- boundFreshIdK
              body' <- bound body
              return $ ValueDK f (vars1 ++ [r]) $
                       foldr (\ (i, x) ->
                                SelectK i (VarK r) x)
                             body'
                             (zip [0..] vars2)
    bound (SwitchK val exprs) =
      SwitchK val <$> mapM bound exprs
    bound (PrimitiveK p vals ids exprs) =
      PrimitiveK p vals ids <$> mapM bound exprs
    bound (ForeignK sig vals id expr) =
      ForeignK sig vals id <$> bound expr

    boundFreshIdK :: BoundParamM IdK
    boundFreshIdK = do
      state <- get
      modify (\ state -> state {
        bpsNextFreshId = bpsNextFreshId state + 1
      })
      return (bpsNextFreshId state)

-- Register allocation

data AllocState =
  AllocState {
    alsNextFreshId :: IdK
  }

data AllocContext =
  AllocContext {
    -- Number of registers available for register allocation
    alsMaxRegisters :: Integer,

    -- Variables in registers
    alsInRegisters :: [IdK],

    -- Current spill record, if any
    alsSpillRecord :: SpillRecord
  }

type AllocM = State AllocState

type SpillRecord = (IdK, [IdK]) -- name + spilled variables

allocateRegisters :: Integer -> ExprK -> ExprK
allocateRegisters numRegisters expr0 =
    let expr' = boundParams (numRegisters - 1) expr0
        (x, _) = runState (alloc initialContext expr') (initialState expr')
     in x
  where
    initialState :: ExprK -> AllocState
    initialState expr =
      AllocState {
        alsNextFreshId = maximum (allIds expr) + 1
      }

    initialContext :: AllocContext
    initialContext =
      AllocContext {
        alsMaxRegisters = numRegisters,
        alsSpillRecord = (
          error ("(allocateRegisters: " ++
                 "no se puede usar un registro spill vacío)"),
          []
        ),
        alsInRegisters  = []
      }

    allocFreshIdK :: AllocM IdK
    allocFreshIdK = do
      state <- get
      modify (\ state -> state {
        alsNextFreshId = alsNextFreshId state + 1
      })
      return (alsNextFreshId state)

    alloc :: AllocContext -> ExprK -> AllocM ExprK
    alloc ctx (LetK decls expr) = do
         decls' <- mapM (allocDecl ctx) decls
         expr'  <- alloc ctx expr
         return $ LetK decls' expr'
       where
         allocDecl :: AllocContext -> DeclarationK -> AllocM DeclarationK
         allocDecl ctx (ValueDK f params body)
           | length' params + 1 > alsMaxRegisters ctx =
             error (
               "(allocateRegisters/allocDecl: la función toma más " ++
               "parámetros que la cantidad de registros disponibles)"
             )
         allocDecl ctx (ValueDK f params body) = do
           ValueDK f params <$>
               alloc
                 (AllocContext {
                   alsMaxRegisters = alsMaxRegisters ctx,
                   alsInRegisters = params,
                   alsSpillRecord = alsSpillRecord ctx
                 })
                 body
    alloc ctx expr
      | not argumentsWillFit || not resultsWillFit =
        error (
          "(allocateRegisters/alloc: los argumentos/resultados no " ++
          "caben en los registros disponibles:\n" ++
          "    " ++ "(" ++ show (alsMaxRegisters ctx) ++ ")\n" ++
          "    " ++ show expr ++
          ")"
        )
      where
        argumentsWillFit :: Bool
        argumentsWillFit =
          argumentsDoNotUseRegisters expr ||
          length' (arguments expr) + 1 <= alsMaxRegisters ctx
        resultsWillFit :: Bool
        resultsWillFit =
          length' (bound expr) + 1 <= alsMaxRegisters ctx
    alloc ctx expr =
        if mustSpillNewRecord
         then allocSpilling
         else allocNotSpilling
      where
        allocSpilling :: AllocM ExprK
        allocSpilling = do
           -- Spill a record
            sv' <- allocFreshIdK
            let newSpillRecord = (sv', liveBefore) in
              RecordK (map (getVar ctx) $ liveBefore) sv' <$>
                      alloc
                        (AllocContext {
                          alsMaxRegisters = alsMaxRegisters ctx,
                          alsInRegisters  = [],
                          alsSpillRecord  = newSpillRecord
                        })
                        expr

        allocNotSpilling :: AllocM ExprK
        allocNotSpilling
          | null fetchedBack || argumentsDoNotUseRegisters expr =
              -- Proceed with the children
              recurAlloc
                 ctx
                 (AllocContext {
                   alsMaxRegisters = alsMaxRegisters ctx,
                   alsInRegisters  = (alsInRegisters ctx `union` bound expr)
                                     `intersect` liveAfter,
                   alsSpillRecord = alsSpillRecord ctx
                 })
                 expr
          | otherwise = do
              -- Fetch one variable
              let v  = head fetchedBack
                  sv = spillRecordVar ctx
                  i  = lookupVarInSpillRecord (head fetchedBack) ctx
               in do
                  v' <- allocFreshIdK
                  SelectK i (VarK sv) v' <$>
                    alloc
                      (AllocContext {
                        alsMaxRegisters = alsMaxRegisters ctx,
                        alsInRegisters  = alsInRegisters ctx ++ [v'],
                        alsSpillRecord  = alsSpillRecord ctx
                      })
                      (replaceExpr v v' expr)
          where
            fetchedBack :: [IdK]
            fetchedBack = arguments expr \\ alsInRegisters ctx

        -- Live variables before and after the root command
        liveBefore :: [IdK]
        liveBefore = (liveAfter \\ bound expr) `union` arguments expr

        liveAfter :: [IdK]
        liveAfter = unionMap freeVars (continuations expr)

        -- Should we spill a new record?
        mustSpillNewRecord :: Bool
        mustSpillNewRecord = not argumentsFit || not resultsFit
          where
            -- One register is always reserved for the spill record
            argumentsFit :: Bool
            argumentsFit =
              argumentsDoNotUseRegisters expr ||
              1 +
              length' (arguments expr `union`
                       (alsInRegisters ctx `intersect` liveAfter)) <=
              alsMaxRegisters ctx
            resultsFit :: Bool
            resultsFit =
              1 +
              length' (bound expr `union`
                       (alsInRegisters ctx `intersect` liveAfter)) <=
              alsMaxRegisters ctx

    getVar :: AllocContext -> IdK -> ValueK
    getVar ctx x
      | x `elem` alsInRegisters ctx = VarK x
      | otherwise =
        let i  = lookupVarInSpillRecord x ctx
         in SelK i (spillRecordVar ctx)

    getValue :: AllocContext -> ValueK -> ValueK
    getValue ctx (VarK x) = getVar ctx x
    getValue ctx val      = val

    spillRecordVar :: AllocContext -> Integer
    spillRecordVar ctx = fst (alsSpillRecord ctx)

    lookupVarInSpillRecord :: IdK -> AllocContext -> Integer
    lookupVarInSpillRecord x ctx =
        case elemIndex x (snd (alsSpillRecord ctx)) of
          Just i  -> fromIntegral i
          Nothing -> error errMsg
      where
        errMsg = "(allocateRegisters: la variable " ++ show x ++
                 " no está guardada en ninguna parte)"

    -- Arguments of records and foreign calls are expected
    -- not to use registers.
    argumentsDoNotUseRegisters :: ExprK -> Bool
    argumentsDoNotUseRegisters (RecordK _ _ _)    = True
    argumentsDoNotUseRegisters (ForeignK _ _ _ _) = True
    argumentsDoNotUseRegisters _                  = False

    recurAlloc :: AllocContext -> AllocContext -> ExprK -> AllocM ExprK
    recurAlloc ctx ctx' (RecordK vals x expr) =
      RecordK (map (getValue ctx) vals) x <$> alloc ctx' expr
    recurAlloc ctx ctx' (SelectK n val id expr) =
      SelectK n (getValue ctx val) id <$> alloc ctx' expr
    recurAlloc ctx ctx' (AppK val vals) =
      return $ AppK (getValue ctx val) (map (getValue ctx) vals)
    recurAlloc _ ctx' (LetK _ _) =
      error "(allocateRegisters/recurAlloc: no debería encontrar un LetK)"
    recurAlloc ctx ctx' (SwitchK val exprs) =
      SwitchK (getValue ctx val) <$> mapM (alloc ctx') exprs
    recurAlloc ctx ctx' (PrimitiveK p vals ids exprs) =
      PrimitiveK p (map (getValue ctx) vals) ids <$> mapM (alloc ctx') exprs
    recurAlloc ctx ctx' (ForeignK sig vals id expr) =
      ForeignK sig (map (getValue ctx) vals) id <$> alloc ctx' expr

    freeVars :: ExprK -> [IdK]
    freeVars expr =
      arguments expr `union`
      (unionMap freeVars (continuations expr) \\ bound expr)

    -- Returns the n free variables that are closest to
    -- the root of the expression
    closestFreeVars :: Integer -> ExprK -> [IdK] -> [IdK]
    closestFreeVars n expr vars =
        take (fromIntegral n) $
        sortBy (comparing (\ v -> Map.findWithDefault 100 v distance)) vars
      where
        distance :: Map.Map IdK Integer
        distance = freeVarsWithDistances expr

    freeVarsWithDistances :: ExprK -> Map.Map IdK Integer
    freeVarsWithDistances expr =
        Map.unionWith max
                  rootVars
                  (Map.map (+1) (childVars `delMany` bound expr))
      where
        rootVars :: Map.Map IdK Integer
        rootVars = Map.fromList [(id, 0) | id <- arguments expr]

        childVars :: Map.Map IdK Integer
        childVars = foldr (Map.unionWith max)
                          Map.empty
                          (map freeVarsWithDistances (continuations expr))

        delMany :: Ord k => Map.Map k a -> [k] -> Map.Map k a
        delMany d ks = foldr Map.delete d ks

    -- Variables used as operands by the root operator
    arguments :: ExprK -> [IdK]
    arguments (RecordK vals _ _)      = unionMap argumentV vals
    arguments (SelectK _ val _ _)     = argumentV val
    arguments (AppK val vals)         = argumentV val `union`
                                        unionMap argumentV vals
    arguments (LetK _ _) =
      error "(allocateRegisters/arguments: no debería encontrar un LetK)"
    arguments (SwitchK val _)         = argumentV val
    arguments (PrimitiveK _ vals _ _) = unionMap argumentV vals
    arguments (ForeignK _ vals _ _)   = unionMap argumentV vals

    argumentV :: ValueK -> [IdK]
    argumentV (VarK x) = [x]
    argumentV _        = []

    -- Variables bound by the root operator
    bound :: ExprK -> [IdK]
    bound (RecordK _ x _)        = [x]
    bound (SelectK _ _ x _)      = [x]
    bound (AppK _ _)             = []
    bound (LetK _ _)             =
      error "(allocateRegisters/bound: no debería encontrar un LetK)"
    bound (SwitchK _ _)          = []
    bound (PrimitiveK _ _ ids _) = ids
    bound (ForeignK _ _ id _)    = [id]

    -- Possible continuation expressions
    continuations :: ExprK -> [ExprK]
    continuations (RecordK _ _ expr)       = [expr]
    continuations (SelectK _ _ _ expr)     = [expr]
    continuations (AppK _ _)               = []
    continuations (LetK _ _)               =
      error "(allocateRegisters/continuations: no debería encontrar un LetK)"
    continuations (SwitchK _ exprs)        = exprs
    continuations (PrimitiveK _ _ _ exprs) = exprs
    continuations (ForeignK _ _ _ expr)    = [expr]

    replaceV :: IdK -> IdK -> ValueK -> ValueK
    replaceV y z (VarK x)
      | x == y    = VarK z
      | otherwise = VarK x
    replaceV y _ (LabelK x)
      | x == y    = error (
                      "(allocateRegisters/replaceV: no debería " ++
                      "reemplazar un nombre de función")
      | otherwise = LabelK x
    replaceV _ _ (SelK _ _) =
                     error (
                      "(allocateRegisters/replaceV: no debería encontrar " ++
                      "un SelK)")
    replaceV _ _ v = v

    replaceExpr :: IdK -> IdK -> ExprK -> ExprK
    replaceExpr v v' (RecordK vals id expr) =
      RecordK (map (replaceV v v') vals) id (replaceExpr v v' expr)
    replaceExpr v v' (SelectK n val id expr) =
      SelectK n (replaceV v v' val) id (replaceExpr v v' expr)
    replaceExpr v v' (AppK val vals) =
      AppK (replaceV v v' val) (map (replaceV v v') vals)
    replaceExpr _ _  (LetK _ _) =
      error "(allocateRegisters/replaceExpr: no debería encontrar un LetK)"
    replaceExpr v v' (SwitchK val exprs) =
      SwitchK (replaceV v v' val) (map (replaceExpr v v') exprs)
    replaceExpr v v' (PrimitiveK p vals ids exprs) =
      PrimitiveK p (map (replaceV v v') vals) ids
                 (map (replaceExpr v v') exprs)
    replaceExpr v v' (ForeignK sig vals id expr) =
      ForeignK sig (map (replaceV v v') vals) id
                   (replaceExpr v v' expr)

----
-- Register assignment

data AssignState =
  AssignState {
    -- Function declarations
    assOldLabelDecls :: Map.Map IdK DeclarationK,

    -- Function declarations after register assignment
    assNewLabelDecls :: Map.Map IdK DeclarationK,

    -- List of register parameters for the given label
    assLabelConvention :: Map.Map IdK [IdK],

    -- Escaping labels: identifiers x such that (LabelK x)
    -- is used other than in subexpressions (AppK (LabelK x) ...)
    assEscapingLabels :: Map.Map IdK (),

    -- Map old identifiers to an identifier in [0..n-1]
    assAssignment :: Map.Map IdK IdK
  }

type AssignM = State AssignState

-- Given an expression in which registers have already been
-- allocated (which means that each subexpression does not need
-- more than n registers), assign them precisely to the
-- variables [0..n-1].
assignRegisters :: Integer -> ExprK -> ExprK
assignRegisters numRegisters expr0 =
    translateLabels (evalState (collectAndAssign expr0) initialState)
  where
    initialState :: AssignState
    initialState =
      AssignState {
        assOldLabelDecls   = Map.empty,
        assNewLabelDecls   = Map.empty,
        assLabelConvention = Map.fromList [
          -- Toplevel continuation receives the result in register 0
          (-1, [0])
        ],
        assEscapingLabels  = Map.empty,
        assAssignment      = Map.empty
      }
    collectAndAssign :: ExprK -> AssignM ExprK
    collectAndAssign expr = do
      collect expr
      assign expr

    escapeV :: ValueK -> AssignM ()
    escapeV (LabelK x) =
      modify (\ state -> state {
        assEscapingLabels = Map.insert x () (assEscapingLabels state)
      })
    escapeV _ = return ()

    -- Determine escaping labels, collect function definitions
    collect :: ExprK -> AssignM ()
    collect (RecordK vals _ expr) = do
      mapM_ escapeV vals
      collect expr
    collect (SelectK _ val _ expr) = do
      escapeV val
      collect expr
    collect (AppK val vals) = do
      -- val does not escape
      mapM_ escapeV vals
    collect (LetK decls expr) = do
        mapM_ collectDecl decls
        collect expr
      where
        collectDecl :: DeclarationK -> AssignM ()
        collectDecl decl@(ValueDK f _ body) = do
          modify (\ state -> state {
            assOldLabelDecls = Map.insert f decl (assOldLabelDecls state)
          })
          collect body
    collect (SwitchK val exprs) = do
      escapeV val
      mapM_ collect exprs
    collect (PrimitiveK _ vals _ exprs) = do
      mapM_ escapeV vals
      mapM_ collect exprs
    collect (ForeignK _ vals _ expr) = do
      mapM_ escapeV vals
      collect expr

    oldLabelDecl :: IdK -> AssignM DeclarationK
    oldLabelDecl f = do
      state <- get
      return $ Map.findWithDefault
                 (error ("(assignRegisters: función no declarada" ++
                         show f ++ ")"))
                 f (assOldLabelDecls state)

    labelConvention :: IdK -> AssignM (Maybe [IdK])
    labelConvention f = do
      state <- get
      return $ Map.lookup f (assLabelConvention state)

    newLabelDecl :: IdK -> AssignM (Maybe DeclarationK)
    newLabelDecl f = do
      state <- get
      return $ Map.lookup f (assNewLabelDecls state)

    isKnownLabel :: IdK -> AssignM Bool
    isKnownLabel x = do
      state <- get
      return . not $ Map.member x (assEscapingLabels state)

    setAssignmentForId :: IdK -> IdK -> AssignM ()
    setAssignmentForId var newVar = do
      state <- get
      case Map.lookup var (assAssignment state) of
        Nothing -> return ()
        Just _  ->
          error (
            "(assignRegisters/setAssignmentForId: ya se le asignó un " ++
            "registro al identificador " ++ show var ++ ")"
          )
      modify (\ state -> state {
        assAssignment = Map.insert var newVar (assAssignment state)
      })

    allRegisters :: [IdK]
    allRegisters = [0..fromIntegral (numRegisters - 1)]

    -- Find a register that is currently not used in the expression
    findFreeRegister :: [ExprK] -> AssignM IdK
    findFreeRegister exprs = do
        us <- unionMapM usedBy exprs
        return $ head (allRegisters \\ us)
      where
        -- Registers currently used by the expression
        usedBy :: ExprK -> AssignM [IdK]
        usedBy (RecordK vals _ expr) = do
          uVals <- unionMapM usedByV vals
          uExpr <- usedBy expr
          return (uVals `union` uExpr)
        usedBy (SelectK _ val _ expr) = do
          uVal  <- usedByV val
          uExpr <- usedBy expr
          return (uVal `union` uExpr)
        usedBy (AppK val vals) = do
          uVal  <- usedByV val
          uVals <- unionMapM usedByV vals
          return (uVal `union` uVals)
        usedBy (LetK _ _) =
          error "(assignRegisters: no debería encontra un LetK)"
        usedBy (SwitchK val exprs) = do
          uVal   <- usedByV val
          uExprs <- unionMapM usedBy exprs
          return (uVal `union` uExprs)
        usedBy (PrimitiveK _ vals _ exprs) = do
          uVals  <- unionMapM usedByV vals
          uExprs <- unionMapM usedBy exprs
          return (uVals `union` uExprs)
        usedBy (ForeignK _ vals _ expr) = do
          uVals <- unionMapM usedByV vals
          uExpr <- usedBy expr
          return (uVals `union` uExpr)

        usedByVar :: IdK -> AssignM [IdK]
        usedByVar x = do
          state <- get
          case Map.lookup x (assAssignment state) of
            Nothing -> return []
            Just x' -> return [x']

        usedByV :: ValueK -> AssignM [IdK]
        usedByV (VarK x)   = usedByVar x
        usedByV (SelK _ x) = usedByVar x
        usedByV _ = return []

    getAssignmentForId :: IdK -> AssignM IdK
    getAssignmentForId var = do
      state <- get
      return $
        Map.findWithDefault
          (error "(assignRegisters: variable no asignada a registro)")
          var
          (assAssignment state)

    assignV :: ValueK -> AssignM ValueK
    assignV (VarK x) = do
      x' <- getAssignmentForId x
      return $ VarK x'
    assignV (SelK i x) = do
      x' <- getAssignmentForId x
      return $ SelK i x'
    assignV v = return v

    assign :: ExprK -> AssignM ExprK
    assign (LetK decls expr) = do
        -- assign the body first, so registers for known functions
        -- are assigned in the order they are visited
        expr' <- assign expr
        mapM_ assignDeclWithDefaultParams decls
        decls' <- mapM newDecl decls
        return $ LetK decls' expr'
      where
        newDecl :: DeclarationK -> AssignM DeclarationK
        newDecl (ValueDK f _ _) = do
          fNewDecl <- newLabelDecl f
          case fNewDecl of
            Nothing ->
              error "(assignRegisters: no se asignaron registros a la función)"
            Just d  -> return d
    assign (RecordK vals id expr) = do
      vals' <- mapM assignV vals
      id'   <- findFreeRegister [expr]
      setAssignmentForId id id'
      RecordK vals' id' <$> assign expr
    assign (SelectK n val id expr) = do
      val' <- assignV val
      id'  <- findFreeRegister [expr]
      setAssignmentForId id id'
      SelectK n val' id' <$> assign expr
    assign (AppK val vals) = do
      val'  <- assignV val
      vals' <- mapM assignV vals
      case val' of
        LabelK f -> do
          known <- isKnownLabel f
          if known
           then do
             fConvention <- labelConvention f
             case fConvention of
               Nothing -> assignKnownDeclaration f vals'
               Just _  -> return ()
           else return ()
        _ -> return ()
      return $ AppK val' vals'
    assign (SwitchK val exprs) = do
      val' <- assignV val
      SwitchK val' <$> mapM assign exprs
    assign (PrimitiveK p vals [] exprs) = do
      vals'  <- mapM assignV vals
      PrimitiveK p vals' [] <$> mapM assign exprs
    assign (PrimitiveK p vals [id] exprs) = do
      vals' <- mapM assignV vals
      id'   <- findFreeRegister exprs
      setAssignmentForId id id'
      PrimitiveK p vals' [id'] <$> mapM assign exprs
    assign (PrimitiveK p _ _ _) = do
      error ("(assignRegisters/assign: " ++
             "la primitiva " ++ show p ++ " tiene más de un resultado)")
    assign (ForeignK sig vals id expr) = do
      vals' <- mapM assignV vals
      id'   <- findFreeRegister [expr]
      setAssignmentForId id id'
      ForeignK sig vals' id' <$> assign expr

    assignKnownDeclaration :: IdK -> [ValueK] -> AssignM ()
    assignKnownDeclaration f args = do
        fDecl <- oldLabelDecl f
        let used = concatMap usedRegisters args
            available = allRegisters \\ used
            newParams = newParamsForArgs args available []
         in
           assignDecl newParams fDecl
      where
        usedRegisters :: ValueK -> [IdK]
        usedRegisters (VarK x) = [x]
        usedRegisters (SelK _ _) =
          error (
            "(assignRegisters/usedRegisters: " ++
            "no debería encontrar un SelK como argumento de una aplicación)"
          )
        usedRegisters _ = []

        newParamsForArgs :: [ValueK] -> [IdK] -> [IdK] -> [IdK]
        newParamsForArgs [] _ _ = []
        newParamsForArgs (VarK x : args) available alreadyUsed
          | x `notElem` alreadyUsed =
              x : newParamsForArgs args available (x : alreadyUsed)
        newParamsForArgs (value : args) available alreadyUsed =
          case available of
            [] -> error (
                    "(assignRegisters/newParamsForArgs: " ++
                    "no hay más registros disponibles)"
                  )
            av : available' ->
              av : newParamsForArgs args available' alreadyUsed

    assignDeclWithDefaultParams :: DeclarationK -> AssignM ()
    assignDeclWithDefaultParams decl@(ValueDK _ params _) =
      assignDecl [0..fromIntegral (length params - 1)] decl

    assignDecl :: [IdK] -> DeclarationK -> AssignM ()
    assignDecl newParams (ValueDK f params body) = do
      fNewDecl <- newLabelDecl f
      case fNewDecl of
        Nothing -> do
          zipWithM_ setAssignmentForId params newParams
          modify (\ state -> state {
            assLabelConvention =
              Map.insert f newParams
              (assLabelConvention state)
          })
          body' <- assign body
          modify (\ state -> state {
            assNewLabelDecls =
              Map.insert f (ValueDK f newParams body')
              (assNewLabelDecls state)
          })
        Just _  -> return ()

    -- Translate labels by the number of registers
    translateLabels :: ExprK -> ExprK
    translateLabels (RecordK vals id expr) =
      RecordK (map translateLabelsV vals) id (translateLabels expr)
    translateLabels (SelectK n val id expr) =
      SelectK n (translateLabelsV val) id (translateLabels expr)
    translateLabels (AppK val vals) =
      AppK (translateLabelsV val) (map translateLabelsV vals)
    translateLabels (LetK decls expr) =
        LetK (map translateLabelsDecl decls)
             (translateLabels expr)
      where
        translateLabelsDecl :: DeclarationK -> DeclarationK
        translateLabelsDecl (ValueDK f args body) =
          ValueDK (translateLabel f) args (translateLabels body)
    translateLabels (SwitchK val exprs) =
      SwitchK (translateLabelsV val) (map translateLabels exprs)
    translateLabels (PrimitiveK p vals ids exprs) =
      PrimitiveK p (map translateLabelsV vals) ids (map translateLabels exprs)
    translateLabels (ForeignK sig vals id expr) =
      ForeignK sig (map translateLabelsV vals) id (translateLabels expr)

    translateLabel :: IdK -> IdK
    translateLabel (-1) = -1
    translateLabel n    = numRegisters + n

    translateLabelsV :: ValueK -> ValueK
    translateLabelsV (LabelK n) = LabelK (translateLabel n)
    translateLabelsV v          = v


unionMap :: Eq b => (a -> [b]) -> [a] -> [b]
unionMap f = foldr union [] . map f

