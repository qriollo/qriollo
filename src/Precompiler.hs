
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

module Precompiler(precompile, precompileOrFail) where

import Control.Monad(zipWithM_)
import qualified Data.Map as Map(Map, empty, insert, lookup, fromList)
import Control.Applicative((<$>), (<*>))
import Control.Monad.Trans.State.Lazy(
        StateT(..), get, modify, runStateT,
    )
import Data.List(nub, sort, span)

import Env(
        Env, envEmpty, envPushFrame, envPopFrame,
        envDefine, envSet, envGet, envFromList,
    )
import Primitive(
        primPackage,
        primReferenceNew, primReferenceDeref, primReferenceAssign,
        primReferenceEq,
        primContinuationCallCC, primContinuationThrow,
        primPutChar,
        isPrimTFunction, primTFunctionDom,
        primTFunctionCod, primTFixnum, primTChar, primTFloat,
        primTString, primTTuple, primTPtr, isPrimTPtr, primTPtrDecoration,
        primTBool,
        primTList, isPrimTList, primTListContents,
        primFixnumAdd, primFixnumSub, primFixnumEq, primFixnumLe,
        primFixnumMul, primFixnumDiv, primFixnumMod,
        primFixnumNe, primFixnumLt, primFixnumGe, primFixnumGt,
        primFixnumLshift, primFixnumRshift,
        primFixnumOrb, primFixnumAndb, primFixnumXorb, primFixnumNotb,
        primCharOrd, primCharChr, primSystemExit,
        primString, primError, primErrorMessage, primErrorOK,
    )
import ExpressionE
import ExpressionL

type ValueEnv = Env QualifId ExprL

data ConstructorInfo =
  ConstructorInfo {
    ciDeclaration :: ConstructorDeclaration,
    ciRepresentation :: ConstructorRepresentation,
    ciSiblings :: [QualifId]
  }
type ConstructorEnv = Map.Map QualifId ConstructorInfo

data PrecState = PrecState {
    prsNextFreshId :: Integer,
    prsBindings :: ValueEnv,
    prsConstructors :: ConstructorEnv
  }
type PrecM a = StateT PrecState (Either String) a

-- precFail should be defined using lift, which seems to have a bug
-- this is a workaround
precFail :: String -> PrecM a
precFail = StateT . const . Left

precGetState :: PrecM PrecState
precGetState = get

precModifyState :: (PrecState -> PrecState) -> PrecM ()
precModifyState = modify

precFreshVarL :: PrecM ExprL
precFreshVarL = do
  state <- precGetState
  precModifyState (\ state ->
    state {
      prsNextFreshId = prsNextFreshId state + 1
    })
  return $ VarL (prsNextFreshId state)

precRefresh :: ExprL -> PrecM ExprL
precRefresh expr = snd <$> rec Map.empty expr
  where
    rec :: Map.Map IdL IdL -> ExprL -> PrecM (Map.Map IdL IdL, ExprL)
    rec dict (VarL x) =
      case Map.lookup x dict of
        Nothing -> return (dict, VarL x)
        Just y  -> return (dict, VarL y)
    rec dict (LamL x b) = do
      VarL x' <- precFreshVarL
      (dict', b') <- rec (Map.insert x x' dict) b
      return (dict', LamL x' b')
    rec dict (PrimitiveL p xs) = do
      (dict', xs') <- reclist dict xs
      return (dict', PrimitiveL p xs')
    rec _ _ = error ("(precRefresh implementado solamente para " ++
                     "permitir la eta expansión de las primitivas)")
    reclist :: Map.Map IdL IdL -> [ExprL] -> PrecM (Map.Map IdL IdL, [ExprL])
    reclist dict0 []     = return (dict0, [])
    reclist dict0 (x:xs) = do
      (dict1, x')  <- rec dict0 x
      (dict2, xs') <- reclist dict1 xs
      return (dict0, x' : xs')

-- Bindings

precModifyBindings :: (ValueEnv -> ValueEnv) -> PrecM ()
precModifyBindings f = precModifyState (\ state ->
  state { prsBindings = f (prsBindings state) })

precBind :: QualifId -> ExprL -> PrecM ()
precBind x e = precModifyBindings (envDefine x e)

precGetBinding :: QualifId -> PrecM ExprL
precGetBinding x = do
  s <- precGetState
  case envGet x (prsBindings s) of
    Just e  -> precRefresh e
    Nothing -> error ("(precGetBinding: variable no ligada: " ++ show x ++ ")")

-- Constructors

precDefineConstructor :: QualifId -> ConstructorInfo -> PrecM ()
precDefineConstructor name info = do
  state <- precGetState
  case Map.lookup name (prsConstructors state) of
    Just info -> error "(precDefineConstructor: constructor ya fue definido)"
    Nothing -> return ()
  precModifyState (\ state ->
    state {
      prsConstructors = Map.insert name info
                                   (prsConstructors state)
    })

precConstructorInfo :: QualifId -> PrecM ConstructorInfo
precConstructorInfo name = do
  state <- precGetState
  case Map.lookup name (prsConstructors state) of
    Just info -> return info
    Nothing   -> error "(precConstructorInfo: constructor no definido)"

--

precPushFrame, precPopFrame :: PrecM ()
precPushFrame = precModifyBindings envPushFrame
precPopFrame  = precModifyBindings envPopFrame

----

-- Constructor representation

chooseConstructorRep :: [ConstructorDeclaration] -> [ConstructorRepresentation]
chooseConstructorRep [ConstructorDeclaration _ []]  = [ConstantCR 0]
chooseConstructorRep [ConstructorDeclaration _ [_]] = [TransparentCR]
chooseConstructorRep [ConstructorDeclaration _ _]   = [UntaggedCR]
chooseConstructorRep cs
  | exactlyOneShouldBeTagged = untaggedConstructorReps
  | otherwise = taggedConstructorReps
  where
    taggedConstructorReps :: [ConstructorRepresentation]
    taggedConstructorReps = zipWith taggedRepresentation cs [0..]

    taggedRepresentation :: ConstructorDeclaration -> Integer ->
                            ConstructorRepresentation
    taggedRepresentation (ConstructorDeclaration _ []) i = ConstantCR i
    taggedRepresentation (ConstructorDeclaration _ _)  i = TaggedCR i

    untaggedConstructorReps :: [ConstructorRepresentation]
    untaggedConstructorReps = map (uncurry untaggedRepresentation)
                                  (zipU cs [0..])
      where
        zipU (c:cs) is
          | shouldBeTagged c = (c, error "") : zipU cs is
        zipU (c:cs) (i:is)   = (c, i) : zipU cs is

    untaggedRepresentation :: ConstructorDeclaration -> Integer ->
                            ConstructorRepresentation
    untaggedRepresentation (ConstructorDeclaration _ []) i = ConstantCR i
    untaggedRepresentation (ConstructorDeclaration _ _)  _ = SafeUntaggedCR

    exactlyOneShouldBeTagged :: Bool
    exactlyOneShouldBeTagged = length (filter shouldBeTagged cs) == 1
    
    shouldBeTagged :: ConstructorDeclaration -> Bool
    shouldBeTagged (ConstructorDeclaration _ []) = False
    shouldBeTagged (ConstructorDeclaration _ _)  = True

construct :: ConstructorRepresentation -> [ExprL] -> ExprL
construct (TaggedCR k)   args  = RecordL (ConstantL (FixnumC k) : args)
construct (ConstantCR k) []    = ConstantL (FixnumC k)
construct UntaggedCR     args  = RecordL args
construct SafeUntaggedCR args  = RecordL args
construct TransparentCR  [arg] = arg
construct RefCR          [arg] = PrimitiveL PrimRef [arg]

deconstruct :: ConstructorRepresentation -> Integer -> ExprL -> ExprL
deconstruct (TaggedCR k)   i e    = SelectL (i + 1) e
deconstruct (ConstantCR k) _ _    =
  error ("(deconstruct: No se puede proyectar " ++ 
         "un constructor constante)")
deconstruct UntaggedCR     i e    = SelectL i e
deconstruct SafeUntaggedCR i e    = SelectL i e
deconstruct TransparentCR  i e
  | i == 0    = e
  | otherwise = error ("(deconstruct: No se puede proyectar " ++
                       "más que la primera componente " ++
                       "de un constructor transparente)")
deconstruct RefCR          i e
  | i == 0    = PrimitiveL PrimDeref [e]
  | otherwise = error ("(deconstruct: No se puede proyectar " ++
                       "más que la primera componente " ++
                       "de una referencia)")

----

precompileDatatypeD :: [Declaration] -> PrecM ()
precompileDatatypeD decls = do
    mapM_ declareDatatype decls
  where
    declareDatatype :: Declaration -> PrecM ()
    declareDatatype (ADatatypeD _ _ _ constructorDecls) =
      let allConstructorNames = map constructorName constructorDecls
          constructorReps = chooseConstructorRep constructorDecls
       in do
        zipWithM_ (declareConstructor allConstructorNames)
                  constructorDecls
                  constructorReps
    declareDatatype _ = return ()

    declareConstructor :: [QualifId] ->
                          ConstructorDeclaration ->
                          ConstructorRepresentation ->
                          PrecM ()
    declareConstructor siblings decl@(ConstructorDeclaration name _) rep = do
      precDefineConstructor
        name
        (ConstructorInfo {
          ciDeclaration = decl,
          ciRepresentation = rep,
          ciSiblings = siblings
        })

    constructorName :: ConstructorDeclaration -> QualifId
    constructorName (ConstructorDeclaration name _) = name

precompileForeignD :: [Declaration] -> PrecM [DeclarationL]
precompileForeignD decls = do
    declLists <- mapM precompileForeign decls
    return $ concat declLists
  where
    precompileForeign :: Declaration -> PrecM [DeclarationL]
    precompileForeign (AForeignD _ lang name ident typ) = do
      typeList <- toForeignFuncType typ

      let argTypes = init typeList
          resType = last typeList
       in do
         vfunc@(VarL func) <- precFreshVarL
         precBind ident vfunc

         vargs <- mapM (const precFreshVarL) argTypes
         return [ValueDL func
                   (flip (foldr LamL) (map unVarL vargs)
                     (ForeignL
                       (ForeignSignature lang name argTypes resType)
                       vargs))]
    precompileForeign _ = return []

    toForeignFuncType :: Type -> PrecM [ForeignType]
    toForeignFuncType t
      | isPrimTFunction t = do
          dom <- toForeign (primTFunctionDom t)
          cod <- toForeignFuncType (primTFunctionCod t)
          return (dom : cod)
      | otherwise = do
          ft <- toForeignWithError t
          return [ft]

    unVarL :: ExprL -> IdL
    unVarL (VarL x) = x

    toForeignWithError :: Type -> PrecM ForeignType
    toForeignWithError t
      | isErrorType t'      = do
           s' <- toForeign (errorTypeArgument t')
           return $ ForeignError s'
      | otherwise           = toForeign t
      where
        t' = eraseAnnotations t

        isErrorType :: Type -> Bool
        isErrorType (AAppT _ (AConstructorT _ q) _) =
          q == QualifId primPackage primError
        isErrorType _ = False

        errorTypeArgument :: Type -> Type
        errorTypeArgument (AAppT _ (AConstructorT _ _) t) = t

    toForeign :: Type -> PrecM ForeignType
    toForeign t
      | t' == primTFixnum   = return ForeignFixnum
      | t' == primTChar     = return ForeignChar
      | t' == primTFloat    = return ForeignFloat
      | t' == primTString   = return ForeignString
      | t' == primTBool     = return ForeignBool
      | isPrimTList t'      = do
          fc <- toForeign $ primTListContents t'
          return $ ForeignList fc
      | isPrimTPtr t'       = return $ ForeignPtr (primTPtrDecoration t')
      | isPrimTPtr t'       = return $ ForeignPtr (primTPtrDecoration t')
      | t' == primTTuple [] = return ForeignUnit
      | otherwise           =
          precFail ("No es un tipo admitido para una declaración gringa: " ++
                    show t')
      where
        t' = eraseAnnotations t

precompileValueD :: [Declaration] -> PrecM [DeclarationL]
precompileValueD decls = do
    mapM_ declareVar decls
    declLists <- mapM precompileVal decls
    return $ concat declLists
  where
    declareVar :: Declaration -> PrecM ()
    declareVar (AValueD _ (QualifId _ "_") _ _) =
      return () -- "_" is never bound
    declareVar (AValueD _ x _ _) = do
      v <- precFreshVarL
      precBind x v
    declareVar _ = return ()

    precompileVal :: Declaration -> PrecM [DeclarationL]
    precompileVal (AValueD _ (QualifId _ "_") _ e) = do
      VarL x' <- precFreshVarL
      e' <- precompileExpr e
      return [ValueDL x' e']
    precompileVal (AValueD _ x _ e) = do
      VarL x' <- precGetBinding x
      e' <- precompileExpr e
      return [ValueDL x' e']
    precompileVal _ = return []

precompileConstructor :: ConstructorDeclaration ->
                         ConstructorRepresentation ->
                         PrecM ExprL
precompileConstructor decl rep = do
    freshVars <- mapM (const precFreshVarL) [1..arity]
    let freshIds = map unVarL freshVars in
      return $
        foldr LamL
              (construct rep freshVars)
              freshIds
  where
    arity :: Integer
    arity = let ConstructorDeclaration _ ts = decl
             in fromIntegral $ length ts
    unVarL :: ExprL -> IdL
    unVarL (VarL x) = x

type PreBranch = ([Pattern], Expr)

precompileMatch :: Expr -> [MatchBranch] -> PrecM ExprL
precompileMatch e bs = do
    v@(VarL x) <- precFreshVarL
    e'         <- precompileExpr e
    matchexp   <- precompileMatchBranches
                    [x]
                    (map convertBranch bs)
                    Nothing
    return $ AppL (LamL x matchexp) e'
  where

    -- Convert the representation of branches
    convertBranch :: MatchBranch -> PreBranch
    convertBranch (MatchBranch p e) = ([p], e)

    precompileMatchBranches :: [IdL] -> [PreBranch] -> Maybe ExprL ->
                               PrecM ExprL
    precompileMatchBranches vars branches dflt
      | not (invariant vars branches) =
          error ("(precompileMatchBranches: invariante roto " ++
                 " vars: " ++ show vars ++
                 " branches: " ++ show branches ++
                 " dflt: " ++ show dflt ++
                 ").")

      | allEmpty branches =
          case (branches, dflt) of
            ([], Nothing) ->
              precFail "El análisis de casos no es exhaustivo."
            ([], Just value) ->
              return value
            ([(_, value)], _) ->
              precompileExpr value
            _ ->
              precFail ("El análisis de casos da lugar a " ++
                        "situaciones inalcanzables.")

      | allTuples branches =
        let k = tupleArity branches in do
           freshVars <- mapM (const precFreshVarL) [0..k - 1]
           let freshIds = map unVarL freshVars in do
             matchexp <- precompileMatchBranches
                           (freshIds ++ tail vars)
                           (map expandTupleBranch branches)
                           dflt
             return $ foldl
                 AppL
                 (foldr LamL matchexp freshIds)
                 (map (\ i -> SelectL i (VarL (head vars)))
                      [0..k - 1])

      | allVariables branches = do
          branches' <- mapM (expandVariableBranch (head vars)) branches
          precompileMatchBranches 
            (tail vars)
            branches'
            dflt

      | allConstants branches =
          let branchesPerConstant = collectSameConstant branches
           in do
             case dflt of
               Just _  -> return ()
               Nothing ->
                 precFail ("El análisis de casos no es exhaustivo " ++
                           "para las constantes")

             branches' <- mapM (\ b -> expandConstantBranch vars b dflt)
                               branchesPerConstant
             return $ MatchL MatchLSpansConstants
                        (VarL (head vars))
                        branches'
                        dflt

      | allConstructors branches =
          let branchesPerConstructor = collectSameConstructor branches
              constructors = map leadingConstructor branches
           in do
             cInfo <- precConstructorInfo (head constructors)

             -- Check double inclusion of expected constructors
             -- and matched constructors

             let sPatExp = all (`elem` ciSiblings cInfo) constructors
                 sExpPat = all (`elem` constructors) (ciSiblings cInfo)
              in do

               -- Constructors in the pattern must be among the expected.
               -- This is a sanity check and should be ensured by typing.
               if sPatExp
                then return ()
                else
                  error ("(precompileMatchBranches: el constructor no " ++
                         "corresponde a la lista de constructores esperada)")

               -- Expected constructors should be matched in the pattern.
               -- If they are not, check that there is a default branch.
               if sExpPat
                then return ()
                else
                  case dflt of
                    Just _  -> return ()
                    Nothing ->
                      precFail ("El análisis de casos no es exhaustivo " ++
                                "para los constructores.")

               let dflt2 = if sExpPat then Nothing else dflt in do

                 branches' <-
                   mapM (\ b -> expandConstructorBranch vars b dflt)
                        branchesPerConstructor
                 siblingRepresentations <- matchLRepresentations branches
                 return $ MatchL
                            (MatchLSpansConstructors siblingRepresentations)
                            (VarL (head vars))
                            branches'
                            dflt

      | otherwise =
          let (branches1, branches2) = uniformSplit branches
           in do
              vf@(VarL f) <- precFreshVarL
              vx@(VarL x) <- precFreshVarL
              expr1 <- precompileMatchBranches vars branches1
                         (Just (AppL vf (ConstantL (FixnumC 0))))
              expr2 <- precompileMatchBranches vars branches2 dflt
              return $
                LetL [ValueDL f (LamL x expr2)] expr1
        where
          uniformSplit branches@(b : _)
            | firstIsTuple       b = span firstIsTuple       branches
            | firstIsVariable    b = span firstIsVariable    branches
            | firstIsConstant    b = span firstIsConstant    branches
            | firstIsConstructor b = span firstIsConstructor branches

    -- Invariant:
    -- for every branch (pats, expr) in branches
    --   length vars == length pats
    invariant :: [IdL] -> [PreBranch] -> Bool
    invariant vars branches =
      all (\ (pats, expr) -> length vars == length pats) branches

    unVarL :: ExprL -> IdL
    unVarL (VarL x) = x

    allEmpty :: [PreBranch] -> Bool
    allEmpty = all (null . fst)

    -- Tuples

    allTuples :: [PreBranch] -> Bool
    allTuples = all firstIsTuple

    firstIsTuple :: PreBranch -> Bool
    firstIsTuple (ATupleP _ _ : _, _) = True
    firstIsTuple _                    = False

    tupleArity :: [PreBranch] -> Integer
    tupleArity ((ATupleP _ subpats : _, _) : _) =
      fromIntegral $ length subpats

    expandTupleBranch :: PreBranch -> PreBranch
    expandTupleBranch (ATupleP _ subpats : pats, expr) =
      (subpats ++ pats, expr)

    -- Variables

    allVariables :: [PreBranch] -> Bool
    allVariables = all firstIsVariable

    firstIsVariable :: PreBranch -> Bool
    firstIsVariable (AVarP _ _ : _, _) = True
    firstIsVariable (AAnyP _ : _, _)   = True
    firstIsVariable _                  = False

    expandVariableBranch :: IdL -> PreBranch -> PrecM PreBranch
    expandVariableBranch freshIdL (AVarP _ var : pats, expr) =
      let freshIdE = QualifId primPackage ("{prec|" ++ show freshIdL ++ "}") 
          freshVarE = naVarE freshIdE
       in do
         precBind freshIdE (VarL freshIdL)
         return (pats, replaceVariableE var freshVarE expr)
    expandVariableBranch freshIdL (AAnyP _ : pats, expr) =
      return (pats, expr)

    -- Constants

    allConstants :: [PreBranch] -> Bool
    allConstants = all firstIsConstant

    firstIsConstant :: PreBranch -> Bool
    firstIsConstant (AConstantP _ _ : _, _) = True
    firstIsConstant _                       = False

    collectSame :: (Eq a, Ord a) => (PreBranch -> a) -> [PreBranch] ->
                                    [[PreBranch]]
    collectSame key branches =
        let sortedKeys = nub (sort (map key branches))
         in map (\ k -> filter (\ branch -> key branch == k) branches)
                sortedKeys

    collectSameConstant :: [PreBranch] -> [[PreBranch]]
    collectSameConstant = collectSame leadingConstant

    leadingConstant :: PreBranch -> Constant
    leadingConstant (AConstantP _ c : _, _) = c

    -- The list of branches must be non-empty,
    -- and all branches must start with the same leading constant.
    expandConstantBranch :: [IdL] -> [PreBranch] -> Maybe ExprL ->
                            PrecM MatchBranchL
    expandConstantBranch vars branches dflt = do
      expr' <- precompileMatchBranches 
                 (tail vars)
                 (map dropLeadingConstant branches)
                 dflt -- Note: dflt might be duplicated
      return $ MatchBranchL
           (ConstantConstructor (leadingConstant (head branches)))
           expr'
      where
        dropLeadingConstant :: PreBranch -> PreBranch
        dropLeadingConstant (_ : pats, expr) = (pats, expr)

    -- Constructors
    allConstructors :: [([Pattern], Expr)] -> Bool
    allConstructors = all firstIsConstructor

    firstIsConstructor :: PreBranch -> Bool
    firstIsConstructor (AConstructorP _ _ _ : _, _) = True
    firstIsConstructor _                            = False

    collectSameConstructor :: [PreBranch] -> [[PreBranch]]
    collectSameConstructor = collectSame leadingConstructor

    leadingConstructor :: PreBranch -> QualifId
    leadingConstructor (AConstructorP _ c _ : _, _) = c

    -- Sibling constructor representations
    matchLRepresentations :: [PreBranch] -> PrecM [ConstructorRepresentation]
    matchLRepresentations branches = do
      cInfo <- precConstructorInfo (leadingConstructor (head branches))
      let siblingNames = ciSiblings cInfo in
        mapM (\ siblingName -> do
                  siblingInfo <- precConstructorInfo siblingName
                  return $ ciRepresentation siblingInfo)
             siblingNames

    -- The list of branches must be non-empty,
    -- and all branches must start with the same leading constructor.
    expandConstructorBranch :: [IdL] -> [PreBranch] -> Maybe ExprL ->
                               PrecM MatchBranchL
    expandConstructorBranch vars branches dflt = do
      k      <- arity
      conrep <- representation
      freshVars <- mapM (const precFreshVarL) [0..k - 1]
      let freshIds = map unVarL freshVars in do
        matchexp <- precompileMatchBranches 
                       (freshIds ++ tail vars)
                       (map dropLeadingConstructor branches)
                       dflt -- Note: dflt might be duplicated
        return $ MatchBranchL
             (DataConstructor conrep)
             (foldl AppL
                   (foldr LamL matchexp freshIds)
                   (map (\ i -> deconstruct conrep i (VarL (head vars)))
                        [0..k - 1]))
      where
        dropLeadingConstructor :: PreBranch -> PreBranch
        dropLeadingConstructor (AConstructorP _ _ subpats : pats, expr) =
          (subpats ++ pats, expr)

        arity :: PrecM Integer
        arity = do
          cInfo <- precConstructorInfo (leadingConstructor (head branches))
          let ConstructorDeclaration _ ts = ciDeclaration cInfo
           in return $ fromIntegral (length ts)

        representation :: PrecM ConstructorRepresentation
        representation = do
          cInfo <- precConstructorInfo (leadingConstructor (head branches))
          return $ ciRepresentation cInfo

precompileExpr :: Expr -> PrecM ExprL
precompileExpr (AVarE _ x)         = precGetBinding x
precompileExpr (AConstructorE _ c)
  | isRef c   =
      precompileConstructor
        (ConstructorDeclaration refNew [dontCare])
        RefCR
  | otherwise = do
      cInfo <- precConstructorInfo c
      precompileConstructor (ciDeclaration cInfo)
                            (ciRepresentation cInfo)
  where
    isRef qualifId = qualifId == refNew
    refNew = QualifId primPackage primReferenceNew
    dontCare :: Type
    dontCare = error "(dontCare: Should not be evaluated)"
precompileExpr (AConstantE _ c)    = return $ ConstantL c
precompileExpr (ALamE _ x e)       = do
  precPushFrame
  v@(VarL x') <- precFreshVarL
  precBind x v
  e' <- precompileExpr e
  precPopFrame
  return $ LamL x' e'
precompileExpr (AAppE _ e1 e2)     =
  AppL <$> precompileExpr e1 <*> precompileExpr e2
precompileExpr (ALetE _ decls e)   = do
  precPushFrame
  foreignDecls <- precompileForeignD decls
  precompileDatatypeD decls
  valueDecls <- precompileValueD decls
  e' <- precompileExpr e
  precPopFrame
  let decls' = foreignDecls ++ valueDecls in
    if null decls'
     then return e'
     else return $ LetL decls' e'
precompileExpr (AMatchE _ e bs)    = do
  precompileMatch e bs
precompileExpr (ATupleE _ es)      = 
  RecordL <$> mapM precompileExpr es
precompileExpr (APlaceholderE _ p) = 
  precFail (
    "¿Por qué no te vas un poquito a cagar?\n" ++
    "Encontré un placeholder (" ++ show p ++ ") al momento " ++
    "de compilar una expresión.\n" ++
    "Esto seguramente se debe a que el valor del programa " ++
    "principal\n" ++
    "depende de cómo se vaya a encarnar una cualidad " ++
    "que no está determinada.\n"
  )

precompile :: Expr -> Either String ExprL
precompile expr =
  case runStateT (precompileExpr expr) initialState of
    Left msg         -> Left msg
    Right (exprL, _) -> Right exprL
  where
    initialState = PrecState {
      prsNextFreshId = 0,
      prsBindings = initialEnv,
      prsConstructors = initialConstructorEnv
    }

    initialEnv :: ValueEnv
    initialEnv = envFromList [
      -- Fixnum arithmetic
      (q primFixnumAdd,
         LamL 0 $ LamL 1 $ PrimitiveL PrimFixnumAdd [VarL 0, VarL 1]),
      (q primFixnumSub,
         LamL 0 $ LamL 1 $ PrimitiveL PrimFixnumSub [VarL 0, VarL 1]),
      (q primFixnumEq,
         LamL 0 $ LamL 1 $ PrimitiveL PrimFixnumEq [VarL 0, VarL 1]),
      (q primFixnumLe,
         LamL 0 $ LamL 1 $ PrimitiveL PrimFixnumLe [VarL 0, VarL 1]),
      --
      (q primFixnumMul,
         LamL 0 $ LamL 1 $ PrimitiveL PrimFixnumMul [VarL 0, VarL 1]),
      (q primFixnumDiv,
         LamL 0 $ LamL 1 $ PrimitiveL PrimFixnumDiv [VarL 0, VarL 1]),
      (q primFixnumMod,
         LamL 0 $ LamL 1 $ PrimitiveL PrimFixnumMod [VarL 0, VarL 1]),
      (q primFixnumNe,
         LamL 0 $ LamL 1 $ PrimitiveL PrimFixnumNe [VarL 0, VarL 1]),
      (q primFixnumLt,
         LamL 0 $ LamL 1 $ PrimitiveL PrimFixnumLt [VarL 0, VarL 1]),
      (q primFixnumGe,
         LamL 0 $ LamL 1 $ PrimitiveL PrimFixnumGe [VarL 0, VarL 1]),
      (q primFixnumGt,
         LamL 0 $ LamL 1 $ PrimitiveL PrimFixnumGt [VarL 0, VarL 1]),
      (q primFixnumLshift,
         LamL 0 $ LamL 1 $ PrimitiveL PrimFixnumLshift [VarL 0, VarL 1]),
      (q primFixnumRshift,
         LamL 0 $ LamL 1 $ PrimitiveL PrimFixnumRshift [VarL 0, VarL 1]),
      (q primFixnumOrb,
         LamL 0 $ LamL 1 $ PrimitiveL PrimFixnumOrb [VarL 0, VarL 1]),
      (q primFixnumAndb,
         LamL 0 $ LamL 1 $ PrimitiveL PrimFixnumAndb [VarL 0, VarL 1]),
      (q primFixnumXorb,
         LamL 0 $ LamL 1 $ PrimitiveL PrimFixnumXorb [VarL 0, VarL 1]),
      (q primFixnumNotb,
         LamL 0 $ PrimitiveL PrimFixnumNotb [VarL 0]),
      -- Characters
      (q primCharOrd,
         LamL 0 $ PrimitiveL PrimCharOrd [VarL 0]),
      (q primCharChr,
         LamL 0 $ PrimitiveL PrimCharChr [VarL 0]),
      (q primSystemExit,
         LamL 0 $ PrimitiveL PrimSystemExit [VarL 0]),
      -- References
      (q primReferenceDeref,
         LamL 0 $ PrimitiveL PrimDeref [VarL 0]),
      (q primReferenceAssign,
         LamL 0 $ LamL 1 $ PrimitiveL PrimAssign [VarL 0, VarL 1]),
      (q primReferenceEq,
         LamL 0 $ LamL 1 $ PrimitiveL PrimReferenceEq [VarL 0, VarL 1]),
      -- Continuations
      (q primContinuationCallCC,
         LamL 0 $ PrimitiveL PrimContinuationCallCC [VarL 0]),
      (q primContinuationThrow,
         LamL 0 $ LamL 1 $ PrimitiveL PrimContinuationThrow [VarL 0, VarL 1]),
      -- I/O
      (q primPutChar,
         LamL 0 $ PrimitiveL PrimPutChar [VarL 0])
     ]

    initialConstructorEnv :: ConstructorEnv
    initialConstructorEnv = Map.fromList [
       -- Reference
       (newRef,
        ConstructorInfo {
          ciDeclaration =
            ConstructorDeclaration newRef [
              error ("(No se debería usar la declaración " ++
                     "del pseudo-constructor Ref)")
            ],
          ciRepresentation = RefCR,
          ciSiblings = [newRef]
        }),
       -- String
        (q primString,
          ConstructorInfo {
            ciDeclaration =
              ConstructorDeclaration (q primString) [
                error ("(No se debería usar la declaración " ++
                       "del pseudo-constructor String)")
              ],
            ciRepresentation = TransparentCR,
            ciSiblings = [q primString]
          }
        ),
       -- Error
        (q primErrorMessage,
          ConstructorInfo {
            ciDeclaration =
              ConstructorDeclaration (q primString) [
                error ("(No se debería usar la declaración " ++
                       "del pseudo-constructor ErrorMessage)")
              ],
            ciRepresentation = TaggedCR 0,
            ciSiblings = [q primErrorMessage, q primErrorOK]
          }
        ),
        (q primErrorOK,
          ConstructorInfo {
            ciDeclaration =
              ConstructorDeclaration (q primString) [
                error ("(No se debería usar la declaración " ++
                       "del pseudo-constructor ErrorOK)")
              ],
            ciRepresentation = TaggedCR 1,
            ciSiblings = [q primErrorMessage, q primErrorOK]
          }
        )
     ]
     where
       newRef :: QualifId
       newRef = QualifId primPackage primReferenceNew

    q :: Id -> QualifId
    q = QualifId primPackage
 
precompileOrFail :: Expr -> ExprL
precompileOrFail expr =
  case precompile expr of
    Left msg -> error msg
    Right x  -> x

