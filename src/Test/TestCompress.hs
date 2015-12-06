
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

module Test.TestCompress(test) where

import Compress(compress)
import Test.Testing(TestResult, testMany)

import ExpressionE
import ExpressionL
import ExpressionK

simpleTestCases :: [(ExprK, ExprK)]
simpleTestCases = [
  (
    LetK [
        ValueDK 1 [] (retK (ConstantK $ FixnumC 10)),
        ValueDK 2 [] (retK (ConstantK $ FixnumC 10))
      ]
      (AppK (LabelK 2) [ConstantK (FixnumC 10)]),
    LetK [
        ValueDK 1 [] (retK (ConstantK $ FixnumC 10))
      ]
      (AppK (LabelK 1) [ConstantK (FixnumC 10)])
  ),
  (
    LetK [
        ValueDK 1 [] (AppK (LabelK 2) []),
        ValueDK 2 [] (AppK (LabelK 2) [])
      ]
      (AppK (LabelK 2) [LabelK 2]),
    LetK [
        ValueDK 1 [] (AppK (LabelK 1) [])
      ]
      (AppK (LabelK 1) [LabelK 1])
  ),
  -- sentinel
  (AppK (LabelK 1) [], AppK (LabelK 1) [])
  ]
  where
    retK val = AppK (LabelK (-1)) [val]

testN :: Int -> TestResult
testN 1 = testMany "TestCompress.simpleTestCases"
                  simpleTestCases
  (\ (_, expected)   -> expected)
  (\ (expression, _) -> compress expression)

test :: TestResult
test = mapM_ testN [1]

