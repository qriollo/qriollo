
module Unify(
        Substitution, substEmpty, unify, substitute, freeMetavars,
        representative
    ) where

import Primitive(isPrimTPtr)
import Control.Monad(zipWithM_, filterM)
import Control.Monad.Trans.State.Lazy(StateT(..), get, modify, runStateT)
import qualified Data.Map as Map(
        Map, empty, insert, delete, lookup, findWithDefault, fromList
    )
import Data.List(union, (\\))

import ExpressionE
import Constraints(
        Constraints(..), InstanceType(..), csSetPlaceholder
    )

------------ Substitutions

type Substitution = Map.Map MetavarId Type

class Substitutable f where
  substitute :: Substitution -> f Annotation-> f Annotation

instance Substitutable AnnotConstrainedType where
  substitute subst (ConstrainedType constraints typ) =
    ConstrainedType (map (substitute subst) constraints)
                    (substitute subst typ)

instance Substitutable AnnotTypeConstraint where
  substitute subst (TypeConstraint cls typ) =
    TypeConstraint cls $ substitute subst typ

instance Substitutable AnnotType where
  substitute subst (AVarT ann ident) =
        AVarT ann ident
  substitute subst (AConstructorT ann ident) =
        AConstructorT ann ident
  substitute subst (AAppT ann t1 t2) =
        AAppT ann (substitute subst t1) (substitute subst t2)
  substitute subst (AMetavarT ann v) =
    case Map.lookup v subst of
      Nothing -> AMetavarT ann v
      Just t  -> substitute subst t

------------ Free metavars

unionMap :: Eq b => (a -> [b]) -> [a] -> [b]
unionMap f = foldr union [] . map f

class FreeMetavars a where
  freeMetavars :: Substitution -> a -> [MetavarId]

instance FreeMetavars a => FreeMetavars [a] where
  freeMetavars subst = unionMap (freeMetavars subst)

instance FreeMetavars (AnnotTypeScheme a) where
  freeMetavars subst (ForallT bound typ) =
    freeMetavars subst typ \\ bound

instance FreeMetavars (AnnotConstrainedType a) where
  freeMetavars subst (ConstrainedType constraints typ) =
    freeMetavars subst constraints `union` freeMetavars subst typ

instance FreeMetavars (AnnotTypeConstraint a) where
  freeMetavars subst (TypeConstraint _ typ) = freeMetavars subst typ

instance FreeMetavars (AnnotType a) where
  freeMetavars subst (AVarT _ _)         = []
  freeMetavars subst (AConstructorT _ _) = []
  freeMetavars subst (AAppT _ t1 t2)     = freeMetavars subst t1 `union`
                                           freeMetavars subst t2
  freeMetavars subst (AMetavarT _ v)     =
    case Map.lookup v subst of
      Nothing -> [v]
      Just t  -> freeMetavars subst t

representative :: Substitution -> Type -> Type
representative subst (AMetavarT ann v) =
    case Map.lookup v subst of
      Nothing -> AMetavarT ann v
      Just t  -> representative subst t
representative _     t = t

------------ Unification algorithm

data UnifyState = UnifyState {
                     usConstraints :: Constraints,
                     usSubstitution :: Substitution
                  }
type UnifyM a = StateT UnifyState (Either String) a

substEmpty :: Substitution
substEmpty = Map.empty

setRepresentative :: MetavarId -> Type -> UnifyM ()
setRepresentative v (AMetavarT _ w)
  | v == w = error ("Error interno -- " ++
                    "no se debe asociar una metavariable a sí misma.")
setRepresentative v t =
    modify (\ state -> state {
             usSubstitution = Map.insert v t (usSubstitution state)
           })

getRepresentative :: Type -> UnifyM Type
getRepresentative (AMetavarT ann v) = do
  state <- get
  let subst = usSubstitution state in
    case Map.lookup v subst of
      Nothing -> return (AMetavarT ann v)
      Just t  -> do
          t' <- getRepresentative t
          setRepresentative v t'
          return t'
getRepresentative t = return t

-- unifFail should be defined using lift, which seems to have a bug
-- this is a workaround
unifFail :: String -> StateT UnifyState (Either String) a
unifFail = StateT . const . Left

occurs :: MetavarId -> Type -> UnifyM Bool
occurs v t = case t of
    AVarT _ _            -> return False
    AConstructorT _ _    -> return False
    AAppT _ t1 t2        -> do
      r1 <- occurs v t1
      r2 <- occurs v t2
      return (r1 || r2)
    AMetavarT _ w        ->
      do t' <- getRepresentative t
         case t' of
           AMetavarT _ w' | w' == v -> return True
           AMetavarT _ _            -> return False
           _                        -> occurs v t'
  where occ' v ts = do occ <- mapM (occurs v) ts
                       return $ or occ

unifGetConstraints :: UnifyM Constraints
unifGetConstraints = do
  state <- get
  return $ usConstraints state

unifGetSubstitution :: UnifyM Substitution
unifGetSubstitution = do
  state <- get
  return $ usSubstitution state

unifModifyConstraints :: (Constraints -> Constraints) -> UnifyM ()
unifModifyConstraints f = do
  modify (\ state ->
    state { usConstraints = f (usConstraints state) })

unifLocalInstancesFor :: MetavarId -> UnifyM [(TypeClass, PlaceholderId)]
unifLocalInstancesFor v = do
  constraints <- unifGetConstraints
  return $ Map.findWithDefault [] v (csLocalInstances constraints)

unifSetLocalInstancesFor :: MetavarId -> [(TypeClass, PlaceholderId)] ->
                            UnifyM ()
unifSetLocalInstancesFor v localInstances = do
  unifModifyConstraints (\ constraints ->
    constraints {
      csLocalInstances = Map.insert v
                                    localInstances
                                    (csLocalInstances constraints)
    })

unifDeleteLocalInstancesFor :: MetavarId -> UnifyM ()
unifDeleteLocalInstancesFor v = do
  unifModifyConstraints (\ constraints ->
    constraints {
      csLocalInstances = Map.delete v (csLocalInstances constraints)
    })

unifSetPlaceholder :: PlaceholderId -> Expr -> UnifyM ()
unifSetPlaceholder plh expr = do
  constraints <- unifGetConstraints
  case csSetPlaceholder plh expr constraints of
    Nothing ->
      error ("(unifSetPlaceholder: El placeholder " ++
             "ya estaba instanciado, no se puede reinstanciar).")
    Just constraints' ->
      unifModifyConstraints (const constraints')

unifGetGlobalInstanceFor :: TypeConstraint -> UnifyM (InstanceType, Expr)
unifGetGlobalInstanceFor goal = do
    constraints <- unifGetConstraints
    results <- filterM (\ (InstanceType _ conclusion, _) ->
                          solvesGoalR goal conclusion)
                       (csGlobalInstances constraints)
    if null results
     then unifFail ("No hay una instancia declarada para " ++
                    show (eraseAnnotations goal))
     else return $ head results
  where
    solvesGoalR :: TypeConstraint -> TypeConstraint -> UnifyM Bool
    solvesGoalR (TypeConstraint cls1 typ1) (TypeConstraint cls2 typ2) = do
      typ1' <- getRepresentative typ1
      typ2' <- getRepresentative typ2
      solvesGoal (TypeConstraint cls1 typ1') (TypeConstraint cls2 typ2')

    solvesGoal :: TypeConstraint -> TypeConstraint -> UnifyM Bool

    -- Applications
    solvesGoal (TypeConstraint cls  t@(AAppT _ _ _))
               (TypeConstraint cls' t'@(AAppT _ _ _)) = do
      b <- sameShapeR t t'
      return (cls == cls' && b)
    solvesGoal (TypeConstraint cls  (AAppT _ _ _)) _ =
      return False

    -- Constructors
    solvesGoal (TypeConstraint cls  t@(AConstructorT _ _))
               (TypeConstraint cls' t'@(AConstructorT _ _)) = do
      b <- sameShapeR t t'
      return (cls == cls' && b)
    solvesGoal (TypeConstraint cls  (AConstructorT _ _)) _ =
      return $ False

    solvesGoal goal _ =
      error ("unifGetConstraints: " ++
             "(No es posible resolver un objetivo de la forma " ++
             show goal ++ ").")

    sameShapeR :: Type -> Type -> UnifyM Bool
    sameShapeR typ1 typ2 = do
      typ1' <- getRepresentative typ1
      typ2' <- getRepresentative typ2
      sameShape typ1' typ2'

    sameShape :: Type -> Type -> UnifyM Bool
    sameShape (AConstructorT _ c) (AConstructorT _ c') = return (c == c')
    sameShape (AAppT _ t1 t2)     (AAppT _ t1' t2')    = sameShapeR t1 t1'
    sameShape _ _ = return False

unifFreshPlaceholder :: UnifyM PlaceholderId
unifFreshPlaceholder = do
  constraints <- unifGetConstraints
  unifModifyConstraints (\ constraints ->
    constraints {
      csNextFreshPlace = 1 + csNextFreshPlace constraints
    })
  return $ csNextFreshPlace constraints

unifSolveConstraints :: TypeConstraint -> PlaceholderId -> UnifyM ()
unifSolveConstraints (TypeConstraint cls typ0) plh = do
  typ <- getRepresentative typ0
  case typ of
    AVarT _ _ -> 
      error ("unifSolveConstraints: (No debería encontrar " ++
             "una variable de tipos en un tipo que se unifica)")
    AMetavarT _ v -> do
      instV <- unifLocalInstancesFor v
      let findCls = filter ((== cls) . fst) instV in
        if null findCls
         then -- The metavariable v did not have this constraint.
              -- Add it with the current placeholder.
              unifSetLocalInstancesFor v ((cls, plh) : instV)
         else -- The metavariable v did have this constraint.
              -- Make the current placeholder point to the old one.
              let (_, plh') = head findCls in
                unifSetPlaceholder plh (naPlaceholderE plh')
    typ -> do
      subst <- unifGetSubstitution
      let typ' = substitute subst typ in do
        (InstanceType assumptions (TypeConstraint _ conclusionTyp), witness) <-
          unifGetGlobalInstanceFor (TypeConstraint cls typ')
        let matching = Map.fromList (matchRule conclusionTyp typ')
            instantiatedAssumptions = map (applyMatch matching) assumptions
         in do
           placeholders <- mapM (const unifFreshPlaceholder) assumptions
           let fullWitness =
                 -- :not_share_instances:
                 foldl naAppE
                       witness
                       (naTupleE [] : map naPlaceholderE placeholders)
            in do
              unifSetPlaceholder plh fullWitness
              zipWithM_ unifSolveConstraints
                        instantiatedAssumptions
                        placeholders
  where
    matchRule :: Type -> Type -> [(QualifId, Type)]
    matchRule (AAppT _ t1 (AVarT _ v)) (AAppT _ t1' t2') =
      (v, t2') : matchRule t1 t1'
    matchRule (AConstructorT _ _) (AConstructorT _ _) = []
    matchRule _ _ = error "(matchRule: Los tipos no tienen la misma forma)."

    applyMatch :: Map.Map QualifId Type -> TypeConstraint -> TypeConstraint
    applyMatch matching (TypeConstraint cls (AVarT ann typ)) =
      case Map.lookup typ matching of
        Nothing   -> error (
                       "(applyMatch: Asunción de instancia libre:\n    " ++
                       show cls ++ "\npara\n    " ++ show typ ++ "\n)."
                     )
        Just typ' -> TypeConstraint cls typ'

unify :: Type -> Type -> Constraints -> Substitution ->
         Either String (Constraints, Substitution)
unify type1 type2 constraints subst =
    case runStateT (u type1 type2) initialState of
      Left msg         -> Left msg
      Right (_, state) -> Right (usConstraints state, usSubstitution state)
  where
    initialState :: UnifyState
    initialState = UnifyState {
                     usConstraints = constraints,
                     usSubstitution = subst
                   }
    u :: Type -> Type -> UnifyM ()
    u t1o t2o = do 
      t1 <- getRepresentative t1o
      t2 <- getRepresentative t2o
      case (t1, t2) of
        (AMetavarT _ v, AMetavarT _ w) | v == w -> return ()
        (AMetavarT _ v, _) -> do
          occ <- occurs v t2
          if occ
           then do
             sub <- unifGetSubstitution
             unifFail (
               "Unificar los tipos te daría un chabón infinito.\n" ++
               "    " ++ show (eraseAnnotations (substitute sub type1)) ++
               "\n" ++
               "    " ++ show (eraseAnnotations (substitute sub type2))
              )
           else do
             setRepresentative v t2 
             localInstV <- unifLocalInstancesFor v
             mapM_ (\ (cls, plh) ->
                      unifSolveConstraints (TypeConstraint cls t2) plh)
                   localInstV
             unifDeleteLocalInstancesFor v
             return ()
        (_, AMetavarT _ _) -> u t2 t1
        (AVarT _ ident1, AVarT _ ident2)
          | ident1 == ident2 -> return ()
        (t1, t2)
          | isPrimTPtr t1 && isPrimTPtr t2 -> return ()
        (AConstructorT _ ident1, AConstructorT _ ident2)
          | ident1 == ident2 -> return ()
        (AAppT _ t1 t2, AAppT _ s1 s2) -> do
            u t1 s1
            u t2 s2
        _ -> do
               sub <- unifGetSubstitution
               unifFail (
                 "No unifican los tipos.\n" ++
                 "    " ++ show (eraseAnnotations (substitute sub type1)) ++
                 "\n" ++
                 "    " ++ show (eraseAnnotations (substitute sub type2))
                )

