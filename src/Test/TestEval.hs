
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

module Test.TestEval(test) where

import Test.Testing(TestResult, testOK, testError, testMany)

import ExpressionE
import ExpressionL
import ExpressionK
import Primitive(primMinFixnum, primMaxFixnum)
import Eval(ValueI(..), eval)

simpleTestCases :: [(ExprK, ValueI)]
simpleTestCases = [
    -- Record
    (
       RecordK [ConstantK (FixnumC 10), ConstantK (FixnumC 20)] 0 $
       RecordK [ConstantK (FixnumC 30), ConstantK (FixnumC 40)] 1 $
       RecordK [VarK 0, VarK 1] 2 $
         retK (VarK 2),
       RecordI [
         RecordI [
           ConstantI (FixnumC 10), ConstantI (FixnumC 20)
         ],
         RecordI [
           ConstantI (FixnumC 30), ConstantI (FixnumC 40)
         ]
       ]
    ),

    -- Record and select
    (
       RecordK [ConstantK (FixnumC 10), ConstantK (FixnumC 20)] 0 $
       RecordK [ConstantK (FixnumC 30), ConstantK (FixnumC 40)] 1 $
       RecordK [VarK 0, VarK 1] 2 $
       SelectK 1 (VarK 2) 3 $
       SelectK 0 (VarK 3) 4 $
         retK (VarK 4),
       ConstantI (FixnumC 30)
    ),

    -- Simple function declaration and application
    (
       LetK [ValueDK 0 [1] (retK (VarK 1))] $
         AppK (VarK 0) [ConstantK (FixnumC 10)],
       ConstantI (FixnumC 10)
    ),

    -- Switch
    (
       SwitchK (ConstantK (FixnumC 2)) [
           retK (ConstantK $ FixnumC 100),
           retK (ConstantK $ FixnumC 110),
           retK (ConstantK $ FixnumC 120)
       ],
       ConstantI (FixnumC 120)
    ),

    -- Primitives: add
    (
       PrimitiveK PrimFixnumAdd [
           ConstantK (FixnumC 432432),
           ConstantK (FixnumC 989399)
       ] [0] [retK (VarK 0)],
       ConstantI (FixnumC 1421831)
    ),

    -- Primitives: add (test fixnum boundaries)
    (
       PrimitiveK PrimFixnumAdd [
           ConstantK (FixnumC (primMaxFixnum - 1)),
           ConstantK (FixnumC 1)
       ] [0] [retK (VarK 0)],
       ConstantI (FixnumC primMaxFixnum)
    ),

    (
       PrimitiveK PrimFixnumAdd [
           ConstantK (FixnumC (primMaxFixnum - 1)),
           ConstantK (FixnumC 2)
       ] [0] [retK (VarK 0)],
       ConstantI (FixnumC primMinFixnum)
    ),

    -- Primitives: sub
    (
       PrimitiveK PrimFixnumSub [
           ConstantK (FixnumC 989399),
           ConstantK (FixnumC 432432)
       ] [0] [retK (VarK 0)],
       ConstantI (FixnumC 556967)
    ),

    -- Primitives: sub (test fixnum boundaries)
    (
       PrimitiveK PrimFixnumSub [
           ConstantK (FixnumC primMinFixnum),
           ConstantK (FixnumC 1)
       ] [0] [retK (VarK 0)],
       ConstantI (FixnumC primMaxFixnum)
    ),

    -- Primitives: eq (equal)
    (
       PrimitiveK PrimFixnumEq [
           ConstantK (FixnumC 1003),
           ConstantK (FixnumC 1003)
       ] [] [retK (ConstantK $ FixnumC 0),
             retK (ConstantK $ FixnumC 1)],
       ConstantI (FixnumC 0)
    ),

    -- Primitives: eq (lesser)
    (
       PrimitiveK PrimFixnumEq [
           ConstantK (FixnumC 1003),
           ConstantK (FixnumC 1004)
       ] [] [retK (ConstantK $ FixnumC 0),
             retK (ConstantK $ FixnumC 1)],
       ConstantI (FixnumC 1)
    ),

    -- Primitives: eq (greater)
    (
       PrimitiveK PrimFixnumEq [
           ConstantK (FixnumC 1005),
           ConstantK (FixnumC 1004)
       ] [] [retK (ConstantK $ FixnumC 0),
             retK (ConstantK $ FixnumC 1)],
       ConstantI (FixnumC 1)
    ),

    -- Primitives: tag (of constant)
    (
       PrimitiveK PrimTag [
           ConstantK (FixnumC 100)
       ] [0] [retK (VarK 0)],
       ConstantI (FixnumC 100)
    ),

    -- Primitives: tag (of record)
    (
       RecordK [ConstantK (FixnumC 100), ConstantK (FixnumC 101)] 0 $
       PrimitiveK PrimTag [
         VarK 0
       ] [1] [retK (VarK 1)],
       ConstantI (FixnumC 100)
    ),

    -- Primitives: boxed (of constant)
    (
       PrimitiveK PrimBoxed [
           ConstantK (FixnumC 100)
       ] [] [retK (ConstantK $ CharC 'b'), retK (ConstantK $ CharC 'u')],
       ConstantI (CharC 'u')
    ),

    -- Primitives: boxed (of record)
    (
       RecordK [ConstantK (FixnumC 100), ConstantK (FixnumC 101)] 7 $
       PrimitiveK PrimBoxed [
           VarK 7
       ] [] [retK (ConstantK $ CharC 'b'), retK (ConstantK $ CharC 'u')],
       ConstantI (CharC 'b')
    ),

    -- Primitives: le (equal)
    (
       PrimitiveK PrimFixnumLe [
         ConstantK (FixnumC 100),
         ConstantK (FixnumC 100)
       ] [] [retK (ConstantK $ FixnumC 1), retK (ConstantK $ FixnumC 0)],
       ConstantI (FixnumC 1)
    ),

    -- Primitives: le (lesser)
    (
       PrimitiveK PrimFixnumLe [
         ConstantK (FixnumC 99),
         ConstantK (FixnumC 100)
       ] [] [retK (ConstantK $ FixnumC 1), retK (ConstantK $ FixnumC 0)],
       ConstantI (FixnumC 1)
    ),

    -- Primitives: le (greater)
    (
       PrimitiveK PrimFixnumLe [
         ConstantK (FixnumC 100),
         ConstantK (FixnumC 99)
       ] [] [retK (ConstantK $ FixnumC 1), retK (ConstantK $ FixnumC 0)],
       ConstantI (FixnumC 0)
    ),

    -- Poor man's multiplication (test recursion)
    (
       LetK [
         ValueDK 0 [1, 2, 3] $
           PrimitiveK PrimFixnumEq [VarK 2, ConstantK (FixnumC 0)] [] [
             AppK (VarK 1) [ConstantK $ FixnumC 0],
             PrimitiveK PrimFixnumSub [VarK 2, ConstantK (FixnumC 1)] [4] [
               LetK [
                   ValueDK 5 [6] $
                   PrimitiveK PrimFixnumAdd [VarK 3, VarK 6] [7]
                              [AppK (VarK 1) [VarK 7]]
               ] $
               AppK (VarK 0) [VarK 5, VarK 4, VarK 3]
             ]
           ],
         ValueDK 99 [98] (retK (VarK 98))
       ] (AppK (VarK 0) [
            VarK 99,
            ConstantK (FixnumC 329),
            ConstantK (FixnumC 9423)
          ]),
       ConstantI (FixnumC 3100167)
    ),

    -- References
    (
        RecordK [ConstantK $ FixnumC 10, ConstantK $ FixnumC 20] 2 $
        PrimitiveK PrimRef [VarK 2] [3] [
           RecordK [ConstantK $ FixnumC 30, ConstantK $ FixnumC 40] 4 $
           PrimitiveK PrimAssign [VarK 3, VarK 4] [5] [
             PrimitiveK PrimDeref [VarK 3] [6] [
                 retK $ VarK 6
             ]
          ]
        ],
        RecordI [ConstantI (FixnumC 30), ConstantI (FixnumC 40)]
    ),

    -- sentinel
    (retK (ConstantK (FixnumC 1)),
     ConstantI (FixnumC 1))
  ]

testN :: Int -> IO (Either String ())
testN 1 = rec 0 simpleTestCases
  where
    rec :: Integer -> [(ExprK, ValueI)] -> IO (Either String ())
    rec _ [] = return $ Right ()
    rec i ((expr, expected) : tests) = do
      obtained <- eval expr
      if expected == obtained
       then rec (i + 1) tests
       else
         return $ Left (
           "Falló el test TestEval.simpleTestCases !! " ++ show i ++ "\n" ++
           "Expresión: " ++ show expr ++ "\n" ++
           "Esperado: " ++ show expected ++ "\n" ++
           "Obtenido: " ++ show obtained ++ "\n")
    
test :: IO (Either String ())
test = testN 1

