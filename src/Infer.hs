
module Infer(infer, inferOrFail, equalModuloRenaming, InferOptions(..)) where

import Control.Monad(zipWithM, zipWithM_)
import Control.Monad.Trans.State.Lazy(
        State, StateT(..), get, put, modify, evalState, evalStateT,
        runState, runStateT
    )
import qualified Data.Map as Map(
        Map, empty, insert, lookup, findWithDefault, fromList
    )
import Data.Either(lefts, rights)
import Data.List(union, (\\), sort)

import Position(Position, describePosition, showNearbyCode)
import ExpressionE
import Primitive(
        primPackage, primFunction, primTFixnum, primTChar,
        primTFunction, primTTuple, primBuiltins, primReferenceNew,
    )
import Env(
        Env, envEmpty, envPushFrame, envPopFrame,
        envIsLocallyDefined, envDefine, envSet, envGet, envAllValues
    )
import Constraints(InstanceType(..), Constraints(..), csSetPlaceholder)
import Unify(
        Substitution, substEmpty, unify, substitute, freeMetavars,
        representative
    )

data InferOptions = EnforceValueRestriction
                  | DoNotEnforceValueRestriction

type Context = Env QualifId TypeScheme

data InferState = InferState {
    insOptions :: InferOptions,
    insPositionStack :: [Position],

    insNextFreshId :: Integer,
    insSubstitution :: Substitution, -- maps type metavariables to types 
    insContext :: Context,           -- maps value identifiers to types

    -- For implementing typeclasses
    insClassDeclaration :: Map.Map TypeClass Declaration,
    insConstraints :: Constraints,
    insDeclaredInstances :: Map.Map (TypeClass, QualifId) ()
  }
type InferM a = StateT InferState (Either String) a

inferGetState :: InferM InferState
inferGetState = get

inferModifyState :: (InferState -> InferState) -> InferM ()
inferModifyState = modify

inferEnterConstruction :: Annotation -> InferM ()
inferEnterConstruction NA = return ()
inferEnterConstruction (AnnotatePosition pos) =
  inferModifyState (\ state -> state {
    insPositionStack = pos : insPositionStack state
  })

inferLeaveConstruction :: Annotation -> InferM ()
inferLeaveConstruction NA = return ()
inferLeaveConstruction (AnnotatePosition pos) =
  inferModifyState (\ state -> state {
    insPositionStack = tail (insPositionStack state)
  })

-- inferFail should be defined using lift, which seems to have a bug
-- this is a workaround
inferFail :: String -> InferM a
inferFail msg = do
  state <- inferGetState
  StateT . const . Left $ (
     msg ++
     positionMessage (insPositionStack state)
   )
  where
    positionMessage [] = ""
    positionMessage (pos : _) =
     "\n\nCerquita de: " ++ describePosition pos ++ ".\n" ++
     "----\n" ++ showNearbyCode pos ++ "\n----\n"

inferGetSubstitution :: InferM Substitution
inferGetSubstitution = do
  state <- inferGetState
  return $ insSubstitution state

inferGetConstraints :: InferM Constraints
inferGetConstraints = do
  state <- inferGetState
  return $ insConstraints state

inferModifyConstraints :: (Constraints -> Constraints) -> InferM ()
inferModifyConstraints f =
  inferModifyState (\ state ->
    state {
      insConstraints = f (insConstraints state)
    })

freshPlaceholder :: InferM PlaceholderId
freshPlaceholder = do
  constraints <- inferGetConstraints
  inferModifyConstraints (\ constraints ->
    constraints {
      csNextFreshPlace = 1 + csNextFreshPlace constraints
    })
  return $ csNextFreshPlace constraints

inferAddGlobalInstanceType :: InstanceType -> Expr -> InferM ()
inferAddGlobalInstanceType instType implementation = do
  inferModifyConstraints (\ constraints ->
    constraints {
      csGlobalInstances = (instType, implementation) :
                          csGlobalInstances constraints
    })

inferAddConstraint :: MetavarId -> TypeClass -> InferM PlaceholderId
inferAddConstraint v cls = do
   plh <- freshPlaceholder
   inferModifyConstraints (\ constraints ->
     constraints {
       csLocalInstances =
         let d = csLocalInstances constraints in
           Map.insert v ((cls, plh) : Map.findWithDefault [] v d) d
     })
   return plh

inferGetContext :: InferM Context
inferGetContext = do
  state <- inferGetState
  return $ insContext state

inferUnify :: String -> Type -> Type -> InferM ()
inferUnify situation t1 t2 = do
  constraints <- inferGetConstraints
  subst <- inferGetSubstitution
  case unify t1 t2 constraints subst of
    Left msg -> inferFail (situation ++ "\n" ++ msg)
    Right (constraints', subst') ->
      inferModifyState (\ s -> s {
        insSubstitution = subst',
        insConstraints = constraints'
      })

inferUnifyConstrained :: String -> ConstrainedType -> ConstrainedType ->
                         InferM ConstrainedType
inferUnifyConstrained situation
                      (ConstrainedType cs1 t1) (ConstrainedType cs2 t2) = do
  --TODO: constraints?
  inferUnify situation t1 t2
  return $ ConstrainedType cs1 t1

----

freshVarE :: InferM Expr
freshVarE = do
  s <- get
  modify (\ s -> s { insNextFreshId = insNextFreshId s + 1 })
  return $ naVarE (QualifId primPackage
                    ("{infer|" ++ show (insNextFreshId s) ++ "}"))

freshMetavarT :: InferM Type
freshMetavarT = do
  s <- get
  modify (\ s -> s { insNextFreshId = insNextFreshId s + 1 })
  return $ naMetavarT (insNextFreshId s)

inferVariable :: QualifId -> InferM ([PlaceholderId], ConstrainedType)
inferVariable ident = do
    s <- inferGetState
    case envGet ident (insContext s) of
      Just (ForallT mvs ct) -> refreshNames mvs ct
      Nothing -> inferFail (
            "Pará un cachito.\n" ++
            "La variable\n    " ++ show ident ++ "\nno está ligada.")

inferConstructor :: QualifId -> InferM ConstrainedType
inferConstructor ident = do
    s <- inferGetState
    case envGet ident (insContext s) of
      Just (ForallT mvs ct) -> do
        (plhs, ct') <- refreshNames mvs ct
        if null plhs
         then return ct'
         else error ("(inferConstructor: el constructor " ++
                     "no debería tener restricciones).")
      Nothing -> inferFail (
                     "Constructor inexistente:\n    " ++ show ident ++ "\n" ++
                     "Declaralo de una vez."
                 )

refreshNames :: [MetavarId] -> ConstrainedType ->
                InferM ([PlaceholderId], ConstrainedType)
refreshNames origNames ct = do
    freshNames <- mapM (const freshMetavarT) origNames
    let freshNameMap = Map.fromList (zip origNames freshNames)
     in recCT freshNameMap ct
  where
    recCT :: Map.Map MetavarId Type -> ConstrainedType ->
             InferM ([PlaceholderId], ConstrainedType)
    recCT dict (ConstrainedType constraints typ) = do
      placeholdersConstraints <- mapM (recC dict) constraints
      typ' <- recT dict typ
      return (lefts placeholdersConstraints,
              ConstrainedType (rights placeholdersConstraints) typ')

    recC :: Map.Map MetavarId Type -> TypeConstraint ->
            InferM (Either PlaceholderId TypeConstraint)
    recC dict (TypeConstraint cls typ) = do
      subst <- inferGetSubstitution
      case representative subst typ of
        AMetavarT _ v | isRefreshed v -> do
          plh <- case Map.lookup v dict of
                   Just (AMetavarT _ w) ->
                     inferAddConstraint w cls
          return $ Left plh
        _ -> do
          return $ Right (TypeConstraint cls typ)
      where
        isRefreshed v = 
          case Map.lookup v dict of
            Just _  -> True
            Nothing -> False

    recT :: Map.Map MetavarId Type -> Type -> InferM Type
    recT dict (AVarT ann ident) =
      return $ AVarT ann ident
    recT dict (AConstructorT ann ident) =
      return $ AConstructorT ann ident
    recT dict (AAppT ann t1 t2) = do
      t1' <- recT dict t1
      t2' <- recT dict t2
      return (AAppT ann t1' t2')
    recT dict (AMetavarT ann v) = do
      subst <- inferGetSubstitution
      case representative subst (AMetavarT ann v) of
        AMetavarT ann' v' -> case Map.lookup v' dict of
                               Nothing -> return $ AMetavarT ann' v'
                               Just t  -> return t
        t           -> recT dict t

inferModifyContext :: (Context -> Context) -> InferM ()
inferModifyContext f =
    inferModifyState (\ s -> s {
        insContext = f (insContext s)
    })

inferPushFrame, inferPopFrame :: InferM ()
inferPushFrame = inferModifyContext envPushFrame
inferPopFrame  = inferModifyContext envPopFrame

inferDefineLocal :: QualifId -> TypeScheme -> InferM ()
inferDefineLocal (QualifId _ "_") _ = return () -- "_" is never bound
inferDefineLocal ident typ = do
  ctx <- inferGetContext
  if envIsLocallyDefined ident ctx
   then inferFail ("Y dale con " ++ show ident ++ ".\n" ++
                   "La variable\n    " ++ show ident ++ "\nya está ligada.")
   else inferModifyContext (envDefine ident typ)

inferSetLocal :: QualifId -> TypeScheme -> InferM ()
inferSetLocal (QualifId _ "_") _ = return () -- "_" is never bound
inferSetLocal ident typ = inferModifyContext (envSet ident typ)

----

inferDatatypeD :: [Declaration] -> InferM [Declaration]
inferDatatypeD decls = do
    declLists <- mapM introduceConstructors decls
    return $ concat declLists
  where
    introduceConstructors :: Declaration -> InferM [Declaration]
    introduceConstructors
      decl@(ADatatypeD ann typeConstructor typeParams constructors) = do
        mapM_ (introduceConstructor typeConstructor typeParams) constructors
        return [decl]
    introduceConstructors _ = return []

    introduceConstructor :: QualifId -> [QualifId] ->
                            ConstructorDeclaration -> InferM ()
    introduceConstructor
        typeConstructor
        typeParams
        (ConstructorDeclaration constructorName constructorArgs) =
      -- Note: constructors are not allowed to have class constraints
      let constructorType =
            foldr primTFunction
                  (foldl naAppT
                         (naConstructorT typeConstructor)
                         (map naVarT typeParams))
                  constructorArgs 
       in do
         generalizedType <- generalizeAllTypeVars
                              (ConstrainedType [] constructorType)
         inferDefineLocal constructorName generalizedType
         return ()

freeVarsCT :: ConstrainedType -> [QualifId]
freeVarsCT (ConstrainedType constraints typ) =
  foldr union [] (map freeVarsC constraints) `union` freeVarsT typ

freeVarsC :: TypeConstraint -> [QualifId]
freeVarsC (TypeConstraint _ typ) = freeVarsT typ

freeVarsT :: Type -> [QualifId]
freeVarsT (AVarT _ ident)         = [ident]
freeVarsT (AConstructorT _ ident) = []
freeVarsT (AAppT _ t1 t2)         = freeVarsT t1 `union` freeVarsT t2
freeVarsT (AMetavarT _ _)         =
    error "(No debería haber metavariables en el código fuente)."
    
-- Generalize type variables to fresh metavariables.
-- Add constraints on metavariables to the 'local instances' dictionary.
generalizeAllTypeVars :: ConstrainedType -> InferM TypeScheme
generalizeAllTypeVars constrainedType =
  let fvs = freeVarsCT constrainedType in do
    freshIds <- mapM (const freshMetavarT) fvs
    let dict = Map.fromList (zip fvs freshIds)
     in return $ ForallT (map unMetavarT freshIds)
                         (renameCT dict constrainedType)
  where
    unMetavarT :: Type -> MetavarId
    unMetavarT (AMetavarT _ v) = v

    renameCT :: Map.Map QualifId Type -> ConstrainedType -> ConstrainedType
    renameCT dict (ConstrainedType constraints typ) = do
      ConstrainedType (map (renameC dict) constraints) (renameT dict typ)

    renameC :: Map.Map QualifId Type -> TypeConstraint -> TypeConstraint
    renameC dict (TypeConstraint cls t) =
      TypeConstraint cls (renameT dict t)

    renameT :: Map.Map QualifId Type -> Type -> Type
    renameT dict (AVarT ann ident) =
      case Map.lookup ident dict of
        Just t  -> t
        Nothing -> error "(La variable debería estar declarada)."
    renameT _    (AConstructorT ann ident) = AConstructorT ann ident
    renameT dict (AAppT ann t1 t2) = AAppT ann (renameT dict t1)
                                               (renameT dict t2)
    renameT dict (AMetavarT _ _)   =
        error "(No debería haber metavariables en el código fuente)."

datatypeForClass :: TypeClass -> QualifId
datatypeForClass (QualifId qualif ident) =
    QualifId qualif ("{data|" ++ ident ++ "}")

constructorForClass :: TypeClass -> QualifId
constructorForClass (QualifId qualif ident) =
    QualifId qualif ("{cons|" ++ ident ++ "}")

inferDeclareClass :: TypeClass -> Declaration -> InferM ()
inferDeclareClass cls decl = do
  state <- inferGetState
  case Map.lookup cls (insClassDeclaration state) of
    Just _  -> inferFail
                 ("La clase\n    " ++ show cls ++ "\nya estaba declarada.\n" ++
                  "Arreglalo y volvé pebete.")
    Nothing ->
      inferModifyState (\ s ->
        s {
          insClassDeclaration = Map.insert cls decl (insClassDeclaration s)
        })

inferGetClassDeclaration :: TypeClass -> InferM Declaration
inferGetClassDeclaration cls = do
  state <- inferGetState
  case Map.lookup cls (insClassDeclaration state) of
    Nothing   -> inferFail
                   ("La clase\n    " ++ show cls ++ "\nno fue declarada.\n" ++
                    "Andá a saber qué quisiste decir.")
    Just decl -> return decl

-- A declaration:
--
--   class C a where
--     m_1 : (D_1 b_1...) => t_1
--     ...
--     m_N : (D_N b_N...) => t_N
--
-- is turned into a declaration of a datatype:
--
--   data {$C_data} a = {$C_cons} (t_1, ..., t_N)
--
-- plus the definition of several identifiers:
--
--   m_i : (C a, D_i b_i...)  => t_i
--   m_i : {$C_data a} -> {D_i1_data b_i1} -> ... {D_iM_data b_iM} -> t_i
--   m_i ({$C_cons} (t_1, ..., t_N)) d1 ... dM = t_i
--
inferClassD :: [Declaration] -> InferM [Declaration]
inferClassD decls = do
    declLists <- mapM declareClass decls
    return $ concat declLists
  where
    declareClass :: Declaration -> InferM [Declaration]
    declareClass decl@(AClassD ann cls param methDecls) = do
       inferEnterConstruction ann
       checkClassWellFormed decl
       inferDeclareClass cls decl
       mapM_ (declareClassMethod cls param) methDecls
       ms <- zipWithM (methodValueD decl) methDecls [0..]
       inferLeaveConstruction ann
       return ([datatypeDeclaration cls param methDecls] ++ ms)
    declareClass decl = return []

    declareClassMethod :: TypeClass -> QualifId -> MethodDeclaration ->
                          InferM ()
    declareClassMethod cls param
                       (MethodDeclaration
                         meth
                         (ConstrainedType constraints typ)) = do
        methScheme <- generalizeAllTypeVars (ConstrainedType constraints' typ)
        inferDefineLocal meth methScheme
        return ()
      where
        constraints' = TypeConstraint cls (naVarT param) : constraints

    --- NOTE: the methods might have constraints, but the
    --- constructor {$C_cons} does not take them into account.
    --- These are checked when the instance is built.
    datatypeDeclaration :: TypeClass -> QualifId -> [MethodDeclaration] ->
                           Declaration
    datatypeDeclaration cls param methDecls =
      naDatatypeD (datatypeForClass cls) [param]
                  [ConstructorDeclaration
                    (constructorForClass cls)
                    (map methodType methDecls)]
    methodType :: MethodDeclaration -> Type
    methodType (MethodDeclaration _ (ConstrainedType _ typ)) = typ

    methodValueD :: Declaration -> MethodDeclaration ->
                    Integer -> InferM Declaration
    methodValueD (AClassD _ cls param methDecls)
                 (MethodDeclaration meth
                     (ConstrainedType constraints typ)) i = do
      return $
        naValueD meth Nothing
                 (naLamE instArg
                         (naMatchE (naVarE instArg) [
                           MatchBranch
                             (naConstructorP
                               (constructorForClass cls)
                               (map naVarP args))
                             (naVarE (arg i))
                         ]))
      where
        arg j  = QualifId primPackage ("{m|" ++ show j ++ "}")
        args   = map arg [0..length methDecls - 1]
        instArg = QualifId primPackage "{inst}"

    checkClassWellFormed :: Declaration -> InferM ()
    checkClassWellFormed (AClassD ann cls param methDecls) = do
        inferEnterConstruction ann
        mapM_ checkMethDeclWellFormed methDecls
        inferLeaveConstruction ann
      where
        checkMethDeclWellFormed :: MethodDeclaration -> InferM ()
        checkMethDeclWellFormed (MethodDeclaration meth ct) = do
          if constraintsForParam ct
           then inferFail (
                  "El parámetro de la cualidad no puede tener " ++
                  "restricciones adicionales."
                )
           else return ()
          if not (dependsOnParam ct)
           then inferFail (
                  "Esto no es un programa, esto es un mamarracho.\n" ++
                  "El tipo del método\n    " ++ show meth ++ "\n" ++
                  "correspondiente a la cualidad\n    " ++ show cls ++ "\n" ++
                  "debería depender del parámetro\n    " ++ show param
                )
           else return ()
        constraintsForParam :: ConstrainedType -> Bool
        constraintsForParam  (ConstrainedType cs _) =
          not . null $ filter
                         (\ (TypeConstraint _ (AVarT _ v)) -> v == param)
                         cs
        dependsOnParam :: ConstrainedType -> Bool
        dependsOnParam (ConstrainedType _ t) = rec t
          where
            rec (AVarT _ v)         = v == param
            rec (AConstructorT _ _) = False
            rec (AAppT _ t1 t2)     = rec t1 || rec t2
            rec (AMetavarT _ _)     =
              error ("(dependsOnParam: No debería haber metavariables " ++
                     "en el código fuente).")

-- A declaration:
--
--   instance (D_1 b_1, ..., D_m b_m) => C (T a_1 ... a_k) where
--     m_1 = e_1
--     ...
--     m_N = e_N
--
-- is turned into a declaration of a value:
--
--   {$I_instance} :: {$D_1_data} b_1 -> ... -> {$D_m_data} b_m -> {$C_data} a
--   {$I_instance} i_1 ... i_m = {$C_cons} (e_1, ..., e_N)
--
declareInstanceD :: [Declaration] -> InferM ()
declareInstanceD decls = mapM_ declareInstance decls
  where
    declareInstance :: Declaration -> InferM ()
    declareInstance (AInstanceD ann cls
                                instantiatedConstrainedType
                                methImpls) = do
        inferEnterConstruction ann
        classDeclaration <- inferGetClassDeclaration cls
        let instName = instanceNameFor cls instantiatedConstrainedType
            instType@(InstanceType iAssumptions iConclusion) =
              instanceType cls instantiatedConstrainedType
          in do
              tcon <- cTypeConstructor instantiatedConstrainedType
              setInstanceAsDeclared cls tcon
              -- Declare global instance type
              inferAddGlobalInstanceType instType (naVarE instName)
              inferLeaveConstruction ann
    declareInstance _ = return ()

    setInstanceAsDeclared :: TypeClass -> QualifId -> InferM ()
    setInstanceAsDeclared cls tcon = do
      state <- inferGetState
      case Map.lookup (cls, tcon) (insDeclaredInstances state) of
        Nothing -> return ()
        Just _  ->
          inferFail (
            "Si esto es un programa válido yo soy Gardel.\n" ++
            "La cualidad\n    " ++ show cls ++ "\n" ++
            "ya fue encarnada previamente para el constructor\n    " ++
            show tcon
          )
      inferModifyState (\ state ->
        state {
         insDeclaredInstances =
           Map.insert (cls, tcon) ()
                      (insDeclaredInstances state)
        })

    cTypeConstructor :: ConstrainedType -> InferM QualifId
    cTypeConstructor ct@(ConstrainedType _ t) = typeConstructor ct t

    typeConstructor :: ConstrainedType -> Type -> InferM QualifId
    typeConstructor _  (AConstructorT _ c) = return c
    typeConstructor ct (AAppT _ t1 _)      = typeConstructor ct t1
    typeConstructor ct _ =
      inferFail (
        "El tipo para el que se encarna la cualidad " ++
        "tiene que ser de la forma\n" ++
        "    Bolsa coso1 ... cosoN\n" ++
        "donde Bolsa no es un sinónimo.\n" ++
        "Pero pusiste:\n    " ++
        show ct
      )


inferInstanceD :: [Declaration] -> InferM [Declaration]
inferInstanceD decls = do
    declLists <- mapM defineInstance decls
    return $ concat declLists
  where
    defineInstance :: Declaration -> InferM [Declaration]
    defineInstance (AInstanceD ann cls
                                instantiatedConstrainedType
                                methImpls) = do
        inferEnterConstruction ann
        checkConstraintsAreBound $ Just instantiatedConstrainedType
        classDeclaration <- inferGetClassDeclaration cls
        let instName = instanceNameFor cls instantiatedConstrainedType
            instType@(InstanceType iAssumptions iConclusion) =
              instanceType cls instantiatedConstrainedType
          in do
            if not (allMethodsImplemented classDeclaration methImpls)
             then
               inferFail (
                 "Salí de acá.\n    " ++
                 "La encarnación de la cualidad\n    " ++
                 show cls ++ "\n" ++
                 "para el tipo\n    " ++
                 show instantiatedConstrainedType ++ "\n" ++
                 "debería definir todos y solamente los métodos declarados."
               )
             else return ()
            -- Sort methods in the same order as they are declared
            -- in the class
            let sortedMethImpls =
                  map (getMethodImplementation methImpls)
                      (declaredMethodNames classDeclaration)
             in do
              -- Typecheck and convert each method
              exprs <- mapM (methodImplementation
                               classDeclaration
                               instantiatedConstrainedType)
                            sortedMethImpls
              inferLeaveConstruction ann
              return [
                naValueD
                  instName
                  Nothing
                  -- :not_share_instances:
                  (naLamE (QualifId primPackage "_")
                    (foldl naAppE
                           (naConstructorE (constructorForClass cls))
                           exprs))]
    defineInstance decl = return []

    methodImplementation :: Declaration -> ConstrainedType ->
                            MethodImplementation ->
                            InferM Expr
    methodImplementation classDeclaration instantiatedConstrainedType
                         (MethodImplementation meth expr) = do
        (expr', obtainedCType) <- inferExpr expr

        -- This enforces that the implementation of a method
        -- is an instance of the type provided by class.
        ForallT _ freshExpectedCType <- generalizeAllTypeVars expectedCType

        inferUnifyConstrained
          ("La encarnación del método\n    " ++ show meth ++ "\n" ++
           "no coincide con el tipo declarado.\n" ++
           "Me importa un pito si pensás lo contrario.")
          obtainedCType
          freshExpectedCType

        isVal <- expressionIsValue expr
        (newBoundVars, obtainedScheme) <-
            if isVal
             then generalizeConstrainedType obtainedCType
             else return ([], ForallT [] obtainedCType)
        return $ foldr naLamE expr' newBoundVars
      where
        expectedCType :: ConstrainedType
        expectedCType =
          let AClassD _ _ classParam _ = classDeclaration
              MethodDeclaration _ ct = methodDeclaration
           in replaceType classParam instantiatedType ct

        instantiatedType :: Type
        instantiatedType =
          let ConstrainedType _ t = instantiatedConstrainedType in t

        methodDeclaration :: MethodDeclaration
        methodDeclaration =
          let AClassD _ _ _ methDecls = classDeclaration
           in head $ filter ((== meth) . dname) methDecls

        replaceType :: QualifId -> Type -> ConstrainedType -> ConstrainedType
        replaceType x s (ConstrainedType cs t) =
            ConstrainedType (map (repC x s) cs)
                            (repT x s t)
          where
            repC x s (TypeConstraint cls t) =
              TypeConstraint cls (repT x s t)
            repT x s (AVarT ann y)
              | x == y    = s
              | otherwise = AVarT ann y
            repT _ _ t@(AConstructorT _ _) =
                t
            repT x s (AAppT ann t1 t2) =
                AAppT ann (repT x s t1)
                          (repT x s t2)
            repT _ _ (AMetavarT _ _) =
                error ("(repT: No debería haber metavariables " ++
                       "en el código fuente).")

    allMethodsImplemented :: Declaration -> [MethodImplementation] -> Bool
    allMethodsImplemented classDecl impls =
        sort (map dname $ decls classDecl) == sort (map iname impls)
      where
        decls (AClassD _ _ _ methDecls)  = methDecls

    declaredMethodNames :: Declaration -> [QualifId]
    declaredMethodNames classDeclaration =
      let AClassD _ _ _ methDecls = classDeclaration in
        map dname methDecls

    dname :: MethodDeclaration -> QualifId
    dname (MethodDeclaration x _) = x

    iname :: MethodImplementation -> QualifId
    iname (MethodImplementation x _) = x

    getMethodImplementation :: [MethodImplementation] -> QualifId ->
                               MethodImplementation
    getMethodImplementation methImpls methName =
      head $ filter ((== methName) . iname) methImpls

instanceNameFor :: TypeClass -> ConstrainedType -> QualifId 
instanceNameFor cls (ConstrainedType _ t) = 
    QualifId primPackage (mangleQualifs cls (tcon t))
  where
    tcon :: Type -> QualifId
    tcon (AAppT _ t _)       = tcon t
    tcon (AConstructorT _ c) = c
    mangleQualifs :: QualifId -> QualifId -> Id
    mangleQualifs q1 q2 = "{inst|" ++
                          mangleQualifId q1 ++ "|" ++
                          mangleQualifId q2 ++ "}"

instanceType :: TypeClass -> ConstrainedType -> InstanceType
instanceType cls (ConstrainedType cs t) =
    InstanceType cs (TypeConstraint cls t) 

-- Declare the types for each foreign declaration
declareForeignD :: [Declaration] -> InferM [Declaration]
declareForeignD decls = do
    declLists <- mapM declareForeign decls
    return $ concat declLists
  where
    declareForeign :: Declaration -> InferM [Declaration]
    declareForeign decl@(AForeignD _ lang name ident typ) = do
      inferDefineLocal ident (ForallT [] $ ConstrainedType [] typ)
      return [decl]
    declareForeign _ = return []

-- Declare a fresh type for each value declaration
declareValueD :: [Declaration] -> InferM [Maybe ConstrainedType]
declareValueD decls = do
    mapM declareIdent decls
  where
    declareIdent :: Declaration -> InferM (Maybe ConstrainedType)
    declareIdent (AValueD ann x declaredType _) = do
      inferEnterConstruction ann
      -- If the program provides a type for the binding,
      -- use it. Otherwise use a fresh type.
      tXScheme <- case declaredType of
              Nothing -> do
                freshT <- freshMetavarT
                return $ ForallT [] (ConstrainedType [] freshT)
              Just constrainedType ->
                generalizeAllTypeVars constrainedType
      inferDefineLocal x tXScheme
      inferLeaveConstruction ann
      let ForallT _ tX = tXScheme in
        return $ Just tX
    declareIdent _ = return Nothing

-- Check if an expression is a proper value.
-- This is used to enforce ML's value restriction.
expressionIsValue :: Expr -> InferM Bool
expressionIsValue expr = do
  state <- inferGetState
  case insOptions state of
    EnforceValueRestriction ->
      return $ expressionIsValue' expr
    DoNotEnforceValueRestriction ->
      return True

expressionIsValue' :: Expr -> Bool
expressionIsValue' (AVarE _ _)         = True
expressionIsValue' (AConstructorE _ _) = True
expressionIsValue' (AConstantE _ _)    = True
expressionIsValue' (ALamE _ _ _)       = True
expressionIsValue' e@(AAppE _ _ _) =
    let head = exprHead e
        args = exprArgs e
     in case head of
          AConstructorE _ con ->
            con /= QualifId primPackage primReferenceNew &&
            all expressionIsValue' args
          AVarE _ _ -> all expressionIsPlaceholder args
          _ -> False
  where
    exprHead :: Expr -> Expr
    exprHead (AAppE _ e1 _) = exprHead e1
    exprHead e              = e
    exprArgs :: Expr -> [Expr]
    exprArgs (AAppE _ e1 e2) = exprArgs e1 ++ [e2]
    exprArgs _               = []
    expressionIsPlaceholder :: Expr -> Bool
    expressionIsPlaceholder (APlaceholderE _ _) = True
    expressionIsPlaceholder _                   = False
expressionIsValue' (ALetE _ _ _)   = False
expressionIsValue' (AMatchE _ _ _) = False
expressionIsValue' (ATupleE _ es)  = all expressionIsValue' es
expressionIsValue' (APlaceholderE _ _) =
  error "(expressionIsValue: Should not find placeholder)"

inferValueD :: [Declaration] -> [Maybe ConstrainedType] -> InferM [Declaration]
inferValueD decls freshTypes = do
    -- Infer the type of the body of each value declaration
    declsTypes <- zipWithM inferIdent decls freshTypes
    -- Generalize the types of every value declaration
    declsSchemes <- mapM (uncurry generalize) declsTypes
    -- Override the original declarations with the now generalized ones
    declLists <- mapM (uncurry overrideIdentDeclaration) declsSchemes
    return $ concat declLists
  where

    inferIdent :: Declaration -> Maybe ConstrainedType ->
                  InferM (Declaration, Maybe ConstrainedType)
    inferIdent (AValueD ann x declaredType expr) (Just ctExprFresh) = do
      inferEnterConstruction ann
      (expr', ctExpr) <- inferExpr expr
      checkConstraintsAreBound declaredType
      ctExpr' <- inferUnifyConstrained
                   ("Ponete las pilas.\n" ++
                    "El tipo que declarás tiene que coincidir " ++
                    "con el tipo de la cosa.\n" ++
                    "Mirá el tipo del identificador\n    " ++
                    show x)
                   ctExpr
                   ctExprFresh
      inferLeaveConstruction ann
      return (AValueD ann x declaredType expr', Just ctExpr')
    inferIdent decl Nothing = return (decl, Nothing)

    generalize :: Declaration -> Maybe ConstrainedType ->
                  InferM (Declaration, Maybe TypeScheme)
    generalize (AValueD ann x declaredType expr) (Just ctExpr) = do
        gen =<< expressionIsValue expr
      where
        gen :: Bool -> InferM (Declaration, Maybe TypeScheme)
        gen True = do
          inferEnterConstruction ann
          (newBoundVars, scheme) <- generalizeConstrainedType ctExpr
          -- If the user has declared a type, check that it is
          -- an instance of the inferred type
          case declaredType of
            Nothing -> return ()
            Just constrainedType -> do
              userScheme <- generalizeAllTypeVars constrainedType
              subst <- inferGetSubstitution
              if schemeIsInstance subst userScheme scheme
               then return ()
               else inferFail (
                 "  Un día el compilador\n" ++
                 "  taba hinchado las pelotas\n" ++
                 "  y en la salida de error\n" ++
                 "  dijo \"Type mismatch\" idiota.\n\n" ++
                 "Tipo declarado: " ++ showScheme subst userScheme
                 ++ "\n" ++
                 "Tipo inferido:  " ++ showScheme subst scheme
                 ++ "\n")
          inferLeaveConstruction ann
          return (AValueD ann x declaredType
                          (foldr naLamE expr newBoundVars),
                  Just scheme)
          where
            showScheme :: Substitution -> TypeScheme -> String
            showScheme subst (ForallT _ cType) =
              show . eraseAnnotations . substitute subst $ cType
        gen False = do
            inferEnterConstruction ann
            ctExpr' <- case declaredType of
              Nothing -> return ctExpr
              Just constrainedType -> do
                ForallT vs ctUser <- generalizeAllTypeVars constrainedType
                if not (null vs)
                  then
                    inferFail (
                      "Que te ayude Magoya.\n" ++
                      "No se pueden generalizar las variables.\n" ++
                      "La declaración no define un valor propio " ++
                      "(value restriction)."
                    )  
                  else return ()
                inferUnifyConstrained
                  ("Tu declaración me la paso por el culo.\n" ++
                   "El tipo del identificador\n    " ++ show x ++ "\n" ++
                   "no coincide con el tipo declarado.")
                  ctUser
                  ctExpr
            inferLeaveConstruction ann
            return (AValueD ann x declaredType expr, Just $ ForallT [] ctExpr')
    generalize decl Nothing = return (decl, Nothing)

    overrideIdentDeclaration :: Declaration -> Maybe TypeScheme ->
                                InferM [Declaration]
    overrideIdentDeclaration decl@(AValueD _ x _ _) (Just scheme) = do
        inferSetLocal x scheme
        return [decl]
    overrideIdentDeclaration decl Nothing = return []

-- Check that the constraints all refer to variables that
-- occur free in the constrained type. 
-- I.e. forbid things like "Eq a => Int"
checkConstraintsAreBound :: Maybe ConstrainedType -> InferM ()
checkConstraintsAreBound Nothing = return ()
checkConstraintsAreBound (Just (ConstrainedType cs typ))
  | all (`elem` freeVarsT typ) (concatMap freeVarsC cs) = return ()
  | otherwise =
      inferFail (
        "No seas h.d.p.\n" ++
        "Las restricciones de cualidades tienen que referirse\n" ++
        "exclusivamente a variables de tipos que figuren en el tipo."
      )

generalizeConstrainedType :: ConstrainedType -> InferM ([QualifId], TypeScheme)
generalizeConstrainedType ct = do
    subst <- inferGetSubstitution
    ctx <- inferGetContext
    -- Generalize all the free variables in the type which do NOT
    -- occur in the typing context (except for the local frame!).
    let freeVars = freeMetavars subst ct
        usedVars = concatMap (freeMetavars subst)
                             (envAllValues (envPopFrame ctx))
        genVars = freeVars \\ usedVars
     in do
       lst <- mapM closeConstraints genVars
       let constraints2 = concat (map fst lst)
           variables    = concat (map snd lst)
           ConstrainedType constraints1 typ1 = ct
           allConstraints = constraints2 ++ constraints1
        in return (variables,
                   ForallT genVars (ConstrainedType allConstraints typ1))
  where
    closeConstraints :: MetavarId -> InferM ([TypeConstraint], [QualifId])
    closeConstraints v = do
      constraints <- inferGetConstraints
      let clssPlhs = Map.findWithDefault [] v (csLocalInstances constraints)
          clss = map fst clssPlhs
          plhs = map snd clssPlhs
       in do
         freshVars <- mapM (const freshVarE) plhs
         zipWithM_ bindPlaceholder plhs freshVars
         return (map (\ cls -> TypeConstraint cls (naMetavarT v)) clss,
                 map unVarE freshVars)

    unVarE :: Expr -> QualifId
    unVarE (AVarE _ x) = x

    bindPlaceholder :: PlaceholderId -> Expr -> InferM ()
    bindPlaceholder plh expr = do
      constraints <- inferGetConstraints
      case csSetPlaceholder plh expr constraints of
        Nothing ->
            error ("(bindPlaceholder: El placeholder " ++
                   "ya estaba instanciado, no se puede reinstanciar).")
        Just constraints' ->
            inferModifyConstraints (const constraints')

inferExpr :: Expr -> InferM (Expr, ConstrainedType)
inferExpr e@(AVarE ann id) = do
  inferEnterConstruction ann
  (plhs, t) <- inferVariable id
  inferLeaveConstruction ann
  return (foldl naAppE e (map naPlaceholderE plhs), t)
inferExpr e@(AConstructorE ann id) = do
  inferEnterConstruction ann
  t <- inferConstructor id
  inferLeaveConstruction ann
  return (e, t)
inferExpr e@(AConstantE _ (FixnumC _)) = do
  return (e, ConstrainedType [] primTFixnum)
inferExpr e@(AConstantE _ (CharC _)) = do
  return (e, ConstrainedType [] primTChar)
inferExpr (ALamE ann x body) = do
  inferEnterConstruction ann
  inferPushFrame
  tX <- freshMetavarT
  inferDefineLocal x (ForallT [] (ConstrainedType [] tX))
  (body', ConstrainedType cBody tBody) <- inferExpr body
  inferPopFrame
  inferLeaveConstruction ann
  return $ (ALamE ann x body', ConstrainedType cBody (primTFunction tX tBody))
inferExpr (ATupleE ann exprs) = do
   inferEnterConstruction ann
   res <- mapM inferExpr exprs
   inferLeaveConstruction ann
   let exprs'      = map fst res
       constraints = map (toConstraint . snd) res
       types       = map (toType . snd) res
    in
      return (ATupleE ann exprs',
              ConstrainedType (concat constraints) (primTTuple types))
  where
    toConstraint (ConstrainedType c _) = c
    toType (ConstrainedType _ t)       = t
inferExpr (AAppE ann fun arg) = do
  inferEnterConstruction ann
  (fun', ConstrainedType cFun tFun) <- inferExpr fun
  (arg', ConstrainedType cArg tArg) <- inferExpr arg
  tRes <- freshMetavarT
  inferUnify
     ("Esto no tipa ni en pedo.\n" ++
      "El tipo del argumento no coincide con el tipo esperado por la función.")
     (primTFunction tArg tRes)
     tFun
  inferLeaveConstruction ann
  return (AAppE ann fun' arg', ConstrainedType (cFun ++ cArg) tRes)
inferExpr (ALetE ann decls expr) = do
  inferEnterConstruction ann
  inferPushFrame

  -- TODO: type synonyms

  classDecls    <- inferClassD decls
  typeDecls     <- inferDatatypeD decls

  foreignDecls  <- declareForeignD decls
  freshTypes    <- declareValueD decls
  declareInstanceD decls

  instanceDecls <- inferInstanceD decls
  valueDecls    <- inferValueD decls freshTypes

  (expr', ConstrainedType cExpr tExpr) <- inferExpr expr

  inferPopFrame
  inferLeaveConstruction ann

  -- TODO: add constraints coming from declarations
  --       (NB: I think we actually do not need that).
  let decls' = foreignDecls ++ classDecls ++ typeDecls ++
               instanceDecls ++ valueDecls
   in
    return (ALetE ann decls' expr', ConstrainedType cExpr tExpr) --XXX

inferExpr (AMatchE ann target branches) = do
    inferEnterConstruction ann
    (target', ConstrainedType cTarget tTarget) <- inferExpr target
    tRes <- freshMetavarT
    (cBranches, branches') <- inferBranches tTarget tRes branches
    inferLeaveConstruction ann
    return (AMatchE ann target' branches',
            ConstrainedType (cTarget ++ cBranches) tRes)
  where
    inferBranches :: Type -> Type -> [MatchBranch] ->
                     InferM ([TypeConstraint], [MatchBranch])
    inferBranches _  tRes [] = return ([], [])
    inferBranches tTarget tRes (MatchBranch bpat bres : branches) = do
      (cBranch, branch')     <- inferBranch tTarget tRes bpat bres
      (cBranches, branches') <- inferBranches tTarget tRes branches
      return (cBranch ++ cBranches, branch' : branches')

    inferBranch :: Type -> Type -> Pattern -> Expr ->
                   InferM ([TypeConstraint], MatchBranch)
    inferBranch tTarget tRes pat expr = do
      inferPushFrame
      checkPatternWellFormed pat
      patExpr <- patternToExpr pat
      -- Give fresh types to all the variables involved in the patterm
      let fvs = patExprFreeVars patExpr in do
        freshMvs <- mapM (const freshMetavarT) fvs
        zipWithM_ inferDefineLocal fvs
                  (map (ForallT [] . ConstrainedType []) freshMvs)
      -- Infer the type of the pattern
      (_, ConstrainedType cPat tPat) <- inferExpr patExpr
      -- Infer the type of the result of this branch
      (expr', ConstrainedType cExpr tExpr) <- inferExpr expr
      -- Unify:
      inferUnify (
          "No hay poronga que te venga bien.\n" ++
          "El tipo del patrón no coincide con el tipo de la " ++
          "expresión analizada."
        )
        tPat
        tTarget
      inferUnify (
          "Decidite, me tenés las bolas llenas.\n" ++
          "Los tipos de las ramas no coinciden."
        )
        tRes
        tExpr
      -- Leave the frame of this branch
      inferPopFrame
      return (cPat ++ cExpr, MatchBranch pat expr')

    patternToExpr :: Pattern -> InferM Expr
    patternToExpr (AVarP ann x)              = return $ AVarE ann x
    patternToExpr (AConstructorP ann c pats) = do
      exprs <- mapM patternToExpr pats
      return $ foldl (AAppE ann) (AConstructorE ann c) exprs
    patternToExpr (AConstantP ann c)         = return $ AConstantE ann c
    patternToExpr (AAnyP _)                  = freshVarE
    patternToExpr (ATupleP ann pats)         = do
      exprs <- mapM patternToExpr pats
      return $ ATupleE ann exprs

    patExprFreeVars :: Expr -> [QualifId]
    patExprFreeVars (AVarE _ x)         = [x]
    patExprFreeVars (AConstructorE _ _) = []
    patExprFreeVars (AAppE _ e1 e2)     = patExprFreeVars e1 `union`
                                          patExprFreeVars e2
    patExprFreeVars (AConstantE _ _)    = []
    patExprFreeVars (ATupleE _ exps)    = foldr union [] .
                                          map patExprFreeVars $ exps
    patExprFreeVars _                   =
      error "(patExprFreeVars: la expresión no resulta de traducir un patrón)."

    -- Check that the arities of every constructor are fulfilled
    checkPatternWellFormed :: Pattern -> InferM ()
    checkPatternWellFormed (AVarP _ _)              = return ()
    checkPatternWellFormed (AConstructorP ann c pats) = do
      inferEnterConstruction ann
      ConstrainedType _ typ <- inferConstructor c
      let expectedArity = arity typ
          patternArity = length pats
       in do
         if expectedArity /= patternArity
           then inferFail (
                    "Qué hambre.\n" ++
                    "El patrón está mal formado.\n" ++
                    "El constructor\n    " ++ show c ++ "\n" ++
                    "espera " ++ show expectedArity ++ " parámetros, " ++
                    "pero en el patrón figura con " ++ show patternArity ++
                    " parámetros.")
           else mapM_ checkPatternWellFormed pats
         inferEnterConstruction ann
      where
        arity (AAppT _ (AAppT _ (AConstructorT _ fcon) _) t)
          | fcon == QualifId primPackage primFunction
                         = 1 + arity t
        arity _          = 0
    checkPatternWellFormed (AConstantP _ _)         = return ()
    checkPatternWellFormed (AAnyP _)                = return ()
    checkPatternWellFormed (ATupleP _ pats)         = do
      mapM_ checkPatternWellFormed pats

    -- TODO: unfold type synonyms before doing anything else.
    -- Require that they are always given the same number of
    -- arguments they take.

schemeIsInstance :: Substitution -> TypeScheme -> TypeScheme -> Bool
schemeIsInstance subst (ForallT v1 t1) (ForallT v2 t2) = 
    evalState (instCT t1' t2') dict
  where
    dict = Map.fromList (zip vs vs)
    vs = freeMetavars subst t1 \\ v1
    t1' = substitute subst t1
    t2' = substitute subst t2

instanceModuloRenaming :: ConstrainedType -> ConstrainedType -> Bool
instanceModuloRenaming t1 t2 = evalState (instCT t1 t2) Map.empty

equalModuloRenaming :: ConstrainedType -> ConstrainedType -> Bool
equalModuloRenaming t1 t2 = instanceModuloRenaming t1 t2 &&
                            instanceModuloRenaming t2 t1

-- Private: check if a constrained type is an instance of another one

instCT :: ConstrainedType -> ConstrainedType ->
          State (Map.Map MetavarId MetavarId) Bool
instCT (ConstrainedType c1 t1) (ConstrainedType c2 t2) = do
    t  <- instT t1 t2
    cs <- allInstC c2 c1
    return (cs && t)
  where
    allInstC :: [TypeConstraint] -> [TypeConstraint] ->
                State (Map.Map MetavarId MetavarId) Bool
    allInstC []     _  = return True
    allInstC (c:cs) c2 = do
      r  <- isInstC c c2
      rs <- allInstC cs c2
      return (r && rs)
    isInstC :: TypeConstraint -> [TypeConstraint] ->
               State (Map.Map MetavarId MetavarId) Bool
    isInstC c0 [] = return False
    isInstC c0 (c:cs) = do
      r <- instC c0 c
      rs <- isInstC c0 cs
      return (r || rs)

instC :: TypeConstraint -> TypeConstraint ->
         State (Map.Map MetavarId MetavarId) Bool
instC (TypeConstraint c1 t1) (TypeConstraint c2 t2) = do
  if c1 == c2
   then instT t1 t2
   else return False

instT :: Type -> Type -> State (Map.Map MetavarId MetavarId) Bool
instT (AVarT _ i1) (AVarT _ i2) = return (i1 == i2)
instT (AConstructorT _ i1) (AConstructorT _ i2) = return (i1 == i2)
instT (AAppT _ t1 t2) (AAppT _ s1 s2) = do
  r1 <- instT t1 s1
  r2 <- instT t2 s2
  return (r1 && r2)
instT (AMetavarT _ v) (AMetavarT _ w) = do
  dict <- get 
  case Map.lookup v dict of
    Nothing -> do put (Map.insert v w dict)
                  return True
    Just w' -> return (w == w')
instT _ _ = return False

infer :: InferOptions -> Expr -> Either String (Expr, ConstrainedType)
infer inferOptions expr =
  case runStateT (inferExpr expr) initialState of
    Left msg -> Left msg 
    Right ((expr', typ), state) ->
      let subst = insSubstitution state
          constraints = insConstraints state
          placeholderHeap = csPlaceholderHeap (insConstraints state)
       in Right (unfoldPlaceholders placeholderHeap expr',
                annotateConstraints constraints $
                substitute subst typ)
  where
    annotateConstraints :: Constraints -> ConstrainedType -> ConstrainedType
    annotateConstraints constraints (ConstrainedType _ typ) =
      let fvms = freeMetavars substEmpty typ in
        ConstrainedType
          (concatMap (lookupConstraint constraints) fvms)
          typ

    lookupConstraint :: Constraints -> MetavarId -> [TypeConstraint]
    lookupConstraint constraints mv =
      case Map.lookup mv (csLocalInstances constraints) of
        Nothing -> []
        Just cs -> map (\ (cls, _) -> TypeConstraint cls (naMetavarT mv))
                       cs

    initialState :: InferState
    initialState = InferState {
                     insOptions = inferOptions,
                     insPositionStack = [],
                     insNextFreshId = 0,
                     insContext = foldr (uncurry envDefine)
                                        envEmpty
                                        primBuiltins,
                     insSubstitution = substEmpty,
                     insClassDeclaration = Map.empty,
                     insConstraints = Constraints {
                       csGlobalInstances = [],
                       csLocalInstances = Map.empty,
                       csPlaceholderHeap = Map.empty,
                       csNextFreshPlace = 0
                     },
                     insDeclaredInstances = Map.empty
                   }

inferOrFail :: InferOptions -> Expr -> (Expr, ConstrainedType)
inferOrFail inferOptions expr =
  case infer inferOptions expr of
    Left msg     -> error msg 
    Right result -> result

