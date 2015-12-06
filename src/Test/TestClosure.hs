
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

module Test.TestClosure(test) where

import Closure(test_closureConvert, test_closedVars)
import Test.Testing(TestResult, testMany)

import ExpressionE
import ExpressionK

closedVarsTestCases :: [(ExprK, [(IdK, [IdK])])]
closedVarsTestCases = [
  -- 0 refers to 2 as a free var
  (
  RecordK [] 2 $
  LetK [ValueDK 0 [1] (AppK (VarK 1) [VarK 2])]
    (AppK (VarK 0) [ConstantK (FixnumC 10)])
  ,
  [(-1, []), (0, [2])]
  ),

  -- 0 calls 1, so it inherits its free vars
  (
  RecordK [] 2 $
  LetK [ValueDK 1 [] (AppK (VarK 2) [VarK 2])] $
  LetK [ValueDK 0 [] (AppK (VarK 1) [ConstantK (FixnumC 10)])] $
    AppK (VarK 0) [ConstantK (FixnumC 10)]
  ,
  [(-1, []), (0, [2]), (1, [2])]
  ),

  -- 0 and 1 escape
  (
  RecordK [] 2 $
  LetK [ValueDK 0 [] (AppK (VarK 1) [ConstantK (FixnumC 10)]),
        ValueDK 1 [] (AppK (VarK 2) [VarK 2])] $
    AppK (VarK 0) [ConstantK (FixnumC 10)]
  ,
  [(-1, []), (0, []), (1, [2])]
  ),

  -- 0 calls 1, so it inherits its free vars
  (
  RecordK [] 2 $
  LetK [ValueDK 0 []
        (LetK [ValueDK 1 [] (AppK (VarK 2) [VarK 2])]
            (AppK (VarK 1) [ConstantK (FixnumC 10)]))] $
    AppK (VarK 0) [ConstantK (FixnumC 10)]
  ,
  [(-1, []), (0, [2]), (1, [2])]
  ),

  -- 0 does not call 1, so it does not inherit its free vars
  (
  RecordK [] 2 $
  RecordK [] 3 $
  LetK [ValueDK 1 [] (AppK (VarK 2) [VarK 2])] $
  LetK [ValueDK 0 [] (AppK (VarK 3) [ConstantK (FixnumC 10)])] $
    AppK (VarK 0) [ConstantK (FixnumC 10)]
  ,
  [(-1, []), (0, [3]), (1, [2])]
  ),

  -- 0 and 1 escape
  (
  RecordK [] 2 $
  RecordK [] 3 $
  LetK [ValueDK 0 [] (AppK (VarK 3) [ConstantK (FixnumC 10)]),
        ValueDK 1 [] (AppK (VarK 2) [VarK 2])] $
    AppK (VarK 0) [ConstantK (FixnumC 10)]
  ,
  [(-1, []), (0, [3]), (1, [2])]
  ),

  -- 0 does not call 1, so it does not inherit its free vars
  (
  RecordK [] 2 $
  RecordK [] 3 $
  LetK [ValueDK 0 []
        (LetK [ValueDK 1 [] (AppK (VarK 2) [VarK 2])]
            (AppK (VarK 3) [ConstantK (FixnumC 10)]))] $
    AppK (VarK 0) [ConstantK (FixnumC 10)]
  ,
  [(-1, []), (0, [2, 3]), (1, [2])]
  ),

  -- 0 and 1 escape
  (
  RecordK [] 2 $
  RecordK [] 3 $
  LetK [ValueDK 0 [] (AppK (VarK 3) [VarK 1]),
        ValueDK 1 [] (AppK (VarK 2) [VarK 2])] $
    AppK (VarK 0) [ConstantK (FixnumC 10)]
  ,
  [(-1, []), (0, [3]), (1, [2])]
  ),

  -- 0 does not call 1
  (
  RecordK [] 2 $
  RecordK [] 3 $
  LetK [ValueDK 0 []
        (LetK [ValueDK 1 [] (AppK (VarK 2) [VarK 2])]
            (AppK (VarK 3) [VarK 1]))] $
    AppK (VarK 0) [ConstantK (FixnumC 10)]
  ,
  [(-1, []), (0, [2, 3]), (1, [2])]
  ),

  -- Test fixpoint reaching
  (
  RecordK [] 4 $
  RecordK [] 10 $
  RecordK [] 11 $
  RecordK [] 12 $
  RecordK [] 13 $
  LetK [ ValueDK 0 [] (AppK (VarK 1) [VarK 10]) ] $
  LetK [ ValueDK 1 [] (AppK (VarK 2) [VarK 11]) ] $
  LetK [ ValueDK 2 [] (AppK (VarK 3) [VarK 12]) ] $
  LetK [ ValueDK 3 [] (AppK (VarK 4) [VarK 13]) ] $
    AppK (VarK 0) []
  ,
  [(-1, []),
   (0, [4, 10, 11, 12, 13]),
   (1, [4, 11, 12, 13]),
   (2, [4, 12, 13]),
   (3, [4, 13])]
  ),

  -- 0 calls 1, and 1 has 2 as a free variable.
  -- However, 0 does not have 2 as a free variable,
  -- as it is bound inside it.
  (
  RecordK [] 3 $
  LetK [ValueDK 0 [] $
        SelectK 0 (VarK 3) 2 $
        LetK [ValueDK 1 [] (AppK (VarK 2) [])] $
          (retK (ConstantK $ FixnumC 10))
       ]
       (retK (ConstantK $ FixnumC 11))
  ,
  [(-1, []), (0, [3]), (1, [2])]
  ),

  -- Recursive definitions are not free
  (
  LetK [ ValueDK 0 [] (AppK (VarK 0) []) ]
       (AppK (VarK 0) []),
  [(-1, []), (0, [])]
  ),

  -- sentinel
  (retK (VarK 0), [(-1, [])])
  ]

simpleTestCases :: [(ExprK, ExprK)]
simpleTestCases = [
  -- Call escaping function
    (AppK (VarK 0) [],
     SelectK 0 (VarK 0) 1 (AppK (VarK 1) [VarK 0])),

  -- Call known function: trivial case
    (LetK [ValueDK 0 [] (retK (ConstantK (FixnumC 10)))]
          (AppK (VarK 0) []),
     LetK [ValueDK 0 [] (retK (ConstantK (FixnumC 10)))]
          (AppK (VarK 0) [])
    ),

  -- Call known function grabbing a free variable
    (
     RecordK [ConstantK (FixnumC 10)] 0 $
     LetK [ValueDK 1 [] (retK (VarK 0))] $
       AppK (VarK 1) [],
     RecordK [ConstantK (FixnumC 10)] 0 $
     LetK [ValueDK 1 [2] (retK (VarK 2))] $
       AppK (VarK 1) [VarK 0]
    ),

  -- Recursive known function grabbing a free variable
    (
     RecordK [ConstantK (FixnumC 10)] 0 $
     LetK [ValueDK 1 [2] (AppK (VarK 1) [VarK 0])] $
       AppK (VarK 1) [ConstantK (FixnumC 11)],

     RecordK [ConstantK (FixnumC 10)] 0 $
     LetK [ValueDK 1 [2, 3] (AppK (VarK 1) [VarK 3, VarK 3])] $
       AppK (VarK 1) [ConstantK (FixnumC 11), VarK 0]
    ),

  -- Call known function that calls a known function
  -- that grabs a free variable
    (
     RecordK [ConstantK (FixnumC 10)] 0 $
     LetK [ValueDK 1 [] (retK (VarK 0))] $
     LetK [ValueDK 2 [] (AppK (VarK 1) [])] $
       AppK (VarK 2) [],
     --
     RecordK [ConstantK (FixnumC 10)] 0 $
     LetK [ValueDK 1 [3] (retK (VarK 3))] $
     LetK [ValueDK 2 [4] (AppK (VarK 1) [VarK 4])] $
       AppK (VarK 2) [VarK 0]
    ),

  -- Call known function that calls two known functions,
  -- each of which grabs a free variable
    (
     RecordK [ConstantK (FixnumC 10)] 0 $
     LetK [ValueDK 1 [] (retK (VarK 0))] $
     LetK [ValueDK 2 [] (retK (VarK 0))] $
     LetK [ValueDK 3 []
            (SwitchK (ConstantK (FixnumC 2)) [
                AppK (VarK 1) [],
                AppK (VarK 2) []
            ])] $
       AppK (VarK 3) [],
     --
     RecordK [ConstantK (FixnumC 10)] 0 $
     LetK [ValueDK 1 [4] (retK (VarK 4))] $
     LetK [ValueDK 2 [5] (retK (VarK 5))] $
     LetK [ValueDK 3 [6]
            (SwitchK (ConstantK (FixnumC 2)) [
                AppK (VarK 1) [VarK 6],
                AppK (VarK 2) [VarK 6]
            ])] $
       AppK (VarK 3) [VarK 0]
    ),

    (
     RecordK [ConstantK (FixnumC 10)] 0 $
     RecordK [ConstantK (FixnumC 11)] 4 $
     LetK [ValueDK 1 [] (retK (VarK 0))] $
     LetK [ValueDK 2 [] (retK (VarK 4))] $
     LetK [ValueDK 3 []
            (SwitchK (ConstantK (FixnumC 2)) [
                AppK (VarK 1) [],
                AppK (VarK 2) []
            ])] $
       AppK (VarK 3) [],
     --
     RecordK [ConstantK (FixnumC 10)] 0 $
     RecordK [ConstantK (FixnumC 11)] 4 $
     LetK [ValueDK 1 [5] (retK (VarK 5))] $
     LetK [ValueDK 2 [6] (retK (VarK 6))] $
     LetK [ValueDK 3 [7, 8]
            (SwitchK (ConstantK (FixnumC 2)) [
                AppK (VarK 1) [VarK 7],
                AppK (VarK 2) [VarK 8]
            ])] $
       AppK (VarK 3) [VarK 0, VarK 4]
    ),

    (
     RecordK [ConstantK (FixnumC 10)] 0 $
     RecordK [ConstantK (FixnumC 11)] 4 $
     LetK [ValueDK 1 [] (retK (VarK 0))] $
     LetK [ValueDK 2 [] (retK (VarK 4))] $
     LetK [ValueDK 3 [5]
            (SwitchK (ConstantK (FixnumC 2)) [
                AppK (VarK 1) [],
                AppK (VarK 2) [],
                AppK (VarK 5) []
            ])] $
       AppK (VarK 3) [ConstantK (FixnumC 12)],
     --
     RecordK [ConstantK (FixnumC 10)] 0 $
     RecordK [ConstantK (FixnumC 11)] 4 $
     LetK [ValueDK 1 [6] (retK (VarK 6))] $
     LetK [ValueDK 2 [7] (retK (VarK 7))] $
     LetK [ValueDK 3 [5, 8, 9]
            (SwitchK (ConstantK (FixnumC 2)) [
                AppK (VarK 1) [VarK 8],
                AppK (VarK 2) [VarK 9],
                SelectK 0 (VarK 5) 10
                  (AppK (VarK 10) [VarK 5])
            ])] $
       AppK (VarK 3) [ConstantK (FixnumC 12), VarK 0, VarK 4]
    ),

    -- Escaping function
    (
      LetK [ValueDK 0 [1] (retK (VarK 1))] $
      LetK [ValueDK 2 [] (retK (VarK 0))] $ -- make 0 escape
        AppK (VarK 0) [ConstantK (FixnumC 10)]
    ,
      LetK [ValueDK 3 [1, 4] $
                (retK (VarK 1))] $
      RecordK [VarK 3] 0 $
      LetK [ValueDK 2 [5] (retK (VarK 5))] $
        SelectK 0 (VarK 0) 6 $
          AppK (VarK 6) [ConstantK (FixnumC 10), VarK 0]
    ),

{-
    -- Mutually recursive functions (escaping)
    (
      RecordK [] 5 $
      RecordK [] 6 $
      LetK [
              ValueDK 0 [1] (AppK (VarK 3) [VarK 5]),
              ValueDK 3 [4] (AppK (VarK 0) [VarK 6])
           ] $
        retK (ConstantK (FixnumC 10))
    ,
      RecordK [] 5 $
      RecordK [] 6 $
      LetK [
              ValueDK 7 [1, 8] $
                SelectK 1 (VarK 8) 11 $
                SelectK 2 (VarK 8) 12 $
                RecordK [VarK 9, VarK 11, VarK 12] 13 $ -- new closure for 3
                SelectK 0 (VarK 13) 14 $
                (AppK (VarK 14) [VarK 11, VarK 13]),
              ValueDK 9 [4, 10] $
                SelectK 1 (VarK 10) 15 $
                SelectK 2 (VarK 10) 16 $
                RecordK [VarK 7, VarK 15, VarK 16] 17 $ -- new closure for 0
                SelectK 0 (VarK 17) 18 $
                (AppK (VarK 18) [VarK 16, VarK 17])
           ] $
        RecordK [VarK 7, VarK 5, VarK 6] 0 $ -- closure for 0
        RecordK [VarK 9, VarK 5, VarK 6] 3 $ -- closure for 3
        retK (ConstantK (FixnumC 10))
    ),
-}
  -- sentinel
    (retK (VarK 0), retK (VarK 0))
  ]

testN :: Int -> TestResult
testN 1 = testMany "TestClosure.closedVarsTestCases" closedVarsTestCases
  (\ (_, expected)   -> expected)
  (\ (expression, _) -> test_closedVars expression)
testN 2 = testMany "TestClosure.simpleTestCases" simpleTestCases
  (\ (_, expected)   -> expected)
  (\ (expression, _) -> test_closureConvert expression)

test :: TestResult
test = mapM_ testN [1..2]

