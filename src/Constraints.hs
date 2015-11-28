
module Constraints(
        InstanceType(..), Constraints(..), csSetPlaceholder
    ) where

import qualified Data.Map as Map(Map, lookup, insert)

import ExpressionE

-- Datatype for representing the types of instance variables.
--
-- For example
--     "(Ord a, Ord b) => Ord (a, b)"
-- is represented by:
--   InstanceType
--       [
--         TypeConstraint (QualifId _ "Ord") (AVarT _ "a"),
--         TypeConstraint (QualifId _ "Ord") (AVarT _ "b")
--       ]
--       (TypeConstraint (QualifId _ "Ord")
--                       (ATupleT _ (AVarT _ "a")
--                                  (AVarT _ "b")))
--
data InstanceType = InstanceType [TypeConstraint] TypeConstraint
  deriving Show

-- The keys of csLocalInstances must be metavariables
--   ?X
-- such that ?X is not instantiated.
--
-- The value of csLocalInstances for a metavariable  ?X
-- is a list [(C_1, p_1), ..., (C_k, p_k)]
-- meaning that the constraints:
--
--    C_1 ?X
--    ...
--    C_k ?X
--
-- all hold, and p_k is a placeholder for a witness of such constraint.
-- The list must have no duplicated typeclasses, i.e. C_i /= C_j if i /= j.
-- Placeholders in the list must be uninstantiated, i.e. they must not
-- be keys of csPlaceholderHeap.
--
data Constraints = Constraints {
    csGlobalInstances :: [(InstanceType, Expr)],
    csLocalInstances  :: Map.Map MetavarId [(TypeClass, PlaceholderId)],
    csPlaceholderHeap :: Map.Map PlaceholderId Expr,
    csNextFreshPlace  :: Integer
  }
  deriving Show
 
csSetPlaceholder :: PlaceholderId -> Expr -> Constraints ->
                    Maybe Constraints
csSetPlaceholder plh expr constraints =
  case Map.lookup plh (csPlaceholderHeap constraints) of
    Nothing -> Just $
      constraints {
        csPlaceholderHeap =
          Map.insert plh expr (csPlaceholderHeap constraints)
      }
    Just _  -> Nothing

