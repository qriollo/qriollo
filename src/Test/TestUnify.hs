
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

module Test.TestUnify(test) where

import qualified Data.Map as Map(Map, empty, fromList, map)
import Data.Ord(comparing)
import Data.List(sortBy)

import Test.Testing(TestResult, testOK, testError, testMany)

import ExpressionE
import Primitive(primTTuple)
import Constraints(InstanceType(..), Constraints(..))
import Unify(Substitution, substEmpty, unify, substitute)

globalPackage = ["Input"]

qualifyGlobally :: Id -> QualifId
qualifyGlobally = QualifId globalPackage

qualifiedVersion :: (QualifId -> a) -> Id -> a
qualifiedVersion f = f . qualifyGlobally

varT           = qualifiedVersion naVarT
constructorT   = qualifiedVersion naConstructorT
varE           = qualifiedVersion naVarE

simpleTestCases :: [(Type, Type, Bool)]
simpleTestCases = [
  (v, v, True),
  (v, w, True),
  (a, a, True),
  (a, b, False),
  (aOf [a], a, False),
  (a, aOf [a], False),
  (aOf [b, c, a, b, c], aOf [b, c, a, b, c], True),
  (aOf [b, c, a, b, c], aOf [b, a, c, b, c], False),
  (aOf [v, v], aOf [a, a], True),
  (aOf [v, v], aOf [a, b], False),
  (aOf [v, a], aOf [a, v], True),
  (aOf [v, b], aOf [a, v], False),
  (aOf [v, w, a], aOf [a, v, w], True),
  (aOf [v, w, b], aOf [a, v, w], False),
  (aaOf [b, c, a, b, c], aaOf [b, c, a, b, c], True),
  (aaOf [b, c, a, b, c], aaOf [b, a, c, b, c], False),
  (aaOf [v, v], aaOf [a, a], True),
  (aaOf [v, v], aaOf [a, b], False),
  (aaOf [v, a], aaOf [a, v], True),
  (aaOf [v, b], aaOf [a, v], False),
  (aaOf [v, w, a], aaOf [a, v, w], True),
  (aaOf [v, w, b], aaOf [a, v, w], False),
  (primTTuple [b, c, a, b, c], primTTuple [b, c, a, b, c], True),
  (primTTuple [b, c, a, b, c], primTTuple [b, a, c, b, c], False),
  (primTTuple [v, v], primTTuple [a, a], True),
  (primTTuple [v, v], primTTuple [a, b], False),
  (primTTuple [v, a], primTTuple [a, v], True),
  (primTTuple [v, b], primTTuple [a, v], False),
  (primTTuple [v, w, a], primTTuple [a, v, w], True),
  (primTTuple [v, w, b], primTTuple [a, v, w], False),
  (v, aOf [a, w, w], True),
  (primTTuple [v, v], primTTuple [aOf [a, w, w], aOf [w, w, b]], False),
  (primTTuple [v, v], primTTuple [aOf [a, w, w], aOf [w, w, x]], True),
  (primTTuple [v, v], primTTuple [aOf [a, w, w], bOf [a, w, w]], False),
  -- occurs check
  (v, primTTuple [v], False),
  (primTTuple [vv 0, vv 1, vv 2, vv 3],
   primTTuple [vv 1, primTTuple [vv 2], primTTuple [vv 3], vv 0],
   False),
  (primTTuple [vv 0, vv 1, vv 2, vv 3],
   primTTuple [vv 1, primTTuple [vv 2], primTTuple [vv 3], vv 1],
   False),
  (primTTuple [vv 0, vv 1, vv 2, vv 3],
   primTTuple [vv 1, primTTuple [vv 2], primTTuple [vv 3], vv 2],
   False),
  (primTTuple [vv 0, vv 1, vv 2, vv 3],
   primTTuple [vv 1, primTTuple [vv 2], primTTuple [vv 3], vv 3],
   True),
  -- sentinel
  (v, v, True)
 ]
 where v = naMetavarT 0
       w = naMetavarT 1
       x = naMetavarT 2
       vv = naMetavarT
       a = varT "a"
       b = varT "b"
       c = varT "c"
       aOf = foldl naAppT (varT "a")
       bOf = foldl naAppT (varT "b")
       aaOf = foldl naAppT (constructorT "A")
       bbOf = foldl naAppT (constructorT "B")

type GlobalInstances = [(InstanceType, Expr)]
type LocalInstances  = [(MetavarId, [(TypeClass, PlaceholderId)])]
type ResultInstances = [(MetavarId, [(TypeClass, Expr)])]
type PlaceholderRestrictions = [(PlaceholderId, Expr)]

constraintTestCases ::
    [(GlobalInstances,
      LocalInstances,
      Type, Type,
      Either () ResultInstances,
      PlaceholderRestrictions)]
constraintTestCases = [
   ([],
    [ (meta0, [(cEq, place1)]) ],
    v0,
    v0,
    Right [ (meta0, [(cEq, naPlaceholderE place1)]) ],
    []
   ),

   ([],
    [ (meta0, [(cEq, place1)]),
      (meta1, [])
    ],
    v0,
    v1,
    Right [ (meta1, [(cEq, naPlaceholderE place1)]) ],
    []
   ),

   ([],
    [ (meta0, [(cEq, place1)]),
      (meta1, [(cEq, place2)])
    ],
    v0,
    v1,
    Right [ (meta1, [(cEq, naPlaceholderE place2)]) ],
    []
   ),

   ([],
    [ (meta0, [(cEq, place1)]),
      (meta1, [(cOrd, place2)])
    ],
    v0,
    v1,
    Right [ (meta1, [(cOrd, naPlaceholderE place2),
                     (cEq, naPlaceholderE place1)]) ],
    []
   ),

   ([],
    [ (meta0, [(cEq, place1)]),
      (meta1, [(cOrd, place2)])
    ],
    primTTuple [v0, v1],
    primTTuple [v1, v2],
    Right [ (meta2, [(cEq, naPlaceholderE place1),
                     (cOrd, naPlaceholderE place2)]) ],
    []
   ),

   ([],
    [ (meta0, [(cEq, place1)]),
      (meta3, [(cOrd, place2)])
    ],
    primTTuple [v0, v1],
    primTTuple [v2, v3],
    Right [ (meta2, [(cEq, naPlaceholderE place1)]),
            (meta3, [(cOrd, naPlaceholderE place2)]) ],
    []
   ),

   ([],
    [ (meta0, [(cEq, place1)]) ],
    v0,
    primTTuple [v1, v2],
    Left (),
    []
   ),

   ([],
    [ (meta0, [(cEq, place1)]) ],
    v0,
    constructorT "A",
    Left (),
    []
   ),

   -- Eq a => Eq [a]
   ([(InstanceType [TypeConstraint cEq (varT "a")]
                   (TypeConstraint cEq
                      (naAppT (constructorT "Lista")
                              (varT "a"))),
      varE "eq_Lista")],
    [ (meta0, [(cEq, place1)]) ],
    v0,
    naAppT (constructorT "Lista") v1,
    Right [ (meta1, [(cEq, naPlaceholderE freshPlace0)]) ],
    [(place1,
      naAppE (naAppE (varE "eq_Lista") (naTupleE []))
             (naPlaceholderE freshPlace0))]
   ),

   -- Ord Numerito
   -- Ord a, Ord b => Ord (a, b)
   ([
     (InstanceType [
                     TypeConstraint cOrd (varT "a"),
                     TypeConstraint cOrd (varT "b")
                   ]
                   (TypeConstraint cOrd
                      (naAppT
                        (naAppT (constructorT "Par")
                                (varT "a"))
                        (varT "b"))),
      varE "ord_Par"),
     (InstanceType [
                   ]
                   (TypeConstraint cOrd (constructorT "Numerito_")),
      varE "ord_Numerito_")
    ],
    [ (meta0, [(cOrd, place1)]) ],
    v0,
    naAppT (naAppT (constructorT "Par") (constructorT "Numerito_"))
           (constructorT "Numerito_"),
    Right [],
    [(place1, naAppE (naAppE (naAppE (varE "ord_Par") (naTupleE []))
                             (naAppE (varE "ord_Numerito_") (naTupleE [])))
                     (naAppE (varE "ord_Numerito_") (naTupleE [])))]
   ),

   -- Ord Numerito_
   -- Ord a, Ord b => Ord (a, b)
   ([
     (InstanceType [
                     TypeConstraint cOrd (varT "a"),
                     TypeConstraint cOrd (varT "b")
                   ]
                   (TypeConstraint cOrd
                      (naAppT
                        (naAppT (constructorT "Par")
                                (varT "a"))
                        (varT "b"))),
      varE "ord_Par"),
     (InstanceType [
                   ]
                   (TypeConstraint cOrd (constructorT "Numerito_")),
      varE "ord_Numerito_")
    ],
    [ (meta0, [(cOrd, place1)]) ],
    v0,
    naAppT (naAppT (constructorT "Par") (constructorT "Numerito_"))
           (naAppT (naAppT (constructorT "Par") v1) v2),
    Right [ (meta1, [(cOrd, naPlaceholderE freshPlace2)]),
            (meta2, [(cOrd, naPlaceholderE freshPlace3)]) ],
    [
      (place1, naAppE (naAppE (naAppE (varE "ord_Par") (naTupleE []))
                              (naAppE (varE "ord_Numerito_") (naTupleE [])))
                      (naAppE (naAppE (naAppE (varE "ord_Par") (naTupleE []))
                                      (naPlaceholderE freshPlace2))
                              (naPlaceholderE freshPlace3)))
    ]
   ),

   -- sentinel
   ([], [], v0, v0, Right [], [])
 ]
 where meta0  = 0
       v0     = naMetavarT meta0
       meta1  = 1
       v1     = naMetavarT meta1
       meta2  = 2
       v2     = naMetavarT meta2
       meta3  = 3
       v3     = naMetavarT meta3
       cEq    = QualifId [""] "Eq"
       cOrd   = QualifId [""] "Ord"
       place1 = 101
       place2 = 102
       freshPlace0 = 1000
       freshPlace1 = 1001
       freshPlace2 = 1002
       freshPlace3 = 1003

emptyConstraints :: Constraints
emptyConstraints = Constraints {
    csGlobalInstances = [],
    csLocalInstances = Map.empty,
    csPlaceholderHeap = Map.empty,
    csNextFreshPlace = 1000
  }

testN :: Int -> TestResult

testN 1 = rec 0 simpleTestCases
  where
    rec i [] = testOK
    rec i ((type1, type2, expected) : ts)
      | obtained == expected &&
        isUnifier obtained substitution type1 type2
                             = rec (i + 1) ts
      | otherwise =
        testError ("\nFallo el test " ++
                   "(TestUnify.simpleTestCases !! " ++ show i ++ ")" ++
                   "\nAl unificar: " ++ show type1 ++ " " ++ show type2 ++
                   "\nEsperado: " ++ show expected ++
                   "\nObtenido: " ++ show obtained)
      where (substitution, obtained) =
              case unify type1 type2 emptyConstraints substEmpty of
                Left _ -> (substEmpty, False)
                Right (constraints, subst) -> (subst, True)
            isUnifier :: Bool -> Substitution -> Type -> Type -> Bool
            isUnifier False _ _ _      = True
            isUnifier True subst t1 t2 =
                substitute subst t1 == substitute subst t2

testN 2 = rec 0 constraintTestCases
  where
    rec i [] = testOK
    rec i ((globalInsts, localInsts, type1, type2, result, plhRestrs) : ts)
       | not placeholderRestrictionssVerified =
         testError ("\nFallo el test " ++
                    "(TestUnify.constrantTestCases !! " ++ show i ++ ")" ++
                    "\nAl unificar: " ++ show type1 ++ " " ++ show type2 ++
                    "\nNo coinciden las restricciones sobre los placeholders.")
      | obtained == expected = rec (i + 1) ts
      | otherwise =
        testError ("\nFallo el test " ++
                   "(TestUnify.constrantTestCases !! " ++ show i ++ ")" ++
                   "\nAl unificar: " ++ show type1 ++ " " ++ show type2 ++
                   "\nEsperado: " ++ show expected ++
                   "\nObtenido: " ++ show obtained)
      where
        unifResult :: Either String (Constraints, Substitution)
        unifResult = unify type1 type2 initialConstraints substEmpty
          where
            initialConstraints = Constraints {
              csGlobalInstances = globalInsts,
              csLocalInstances  = Map.fromList localInsts,
              csPlaceholderHeap = Map.empty,
              csNextFreshPlace = 1000
            }
        placeholderRestrictionssVerified =
          case unifResult of
            Left _ -> True
            Right (constraints, _) ->
              let heap = csPlaceholderHeap constraints in
                all (\ (plh, expr) ->
                       unfoldPlaceholders heap (naPlaceholderE plh) == expr)
                    plhRestrs
        expected :: Either () (Map.Map MetavarId [(TypeClass, Expr)])
        expected = case result of
                     Left ()     -> Left ()
                     Right insts ->
                       Right $
                       Map.map (sortBy (comparing fst))
                               (Map.fromList insts)
        obtained :: Either () (Map.Map MetavarId [(TypeClass, Expr)])
        obtained =
          case unifResult of
            Left _ -> Left ()
            Right (constraints, _) ->
              let heap = csPlaceholderHeap constraints in
                Right $
                Map.map (sortBy (comparing fst) .
                         map
                          (\ (cls, plh) ->
                             (cls,
                               unfoldPlaceholders
                                 heap
                                 (naPlaceholderE plh))))
                        (csLocalInstances constraints)

test :: TestResult
test = mapM_ testN [1..2]

