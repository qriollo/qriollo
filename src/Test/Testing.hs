
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

module Test.Testing(TestResult, testOK, testError, testMany) where

type TestResult = Either String ()

testOK = Right ()
testError = Left

testMany :: (Eq result, Show test, Show result) =>  
            String -> [test] -> (test -> result) -> (test -> result) ->
            TestResult
testMany suiteName tests expected obtained = rec 0 tests
  where
    rec _ []           = testOK
    rec i (test:tests)
      | e == o    = rec (i + 1) tests
      | otherwise =
          testError ("\nFallo el test " ++
                     "(" ++ suiteName ++ " !! " ++ show i ++ ")" ++
                     "\nTest: " ++ show test ++
                     "\nEsperado: " ++ show e ++
                     "\nObtenido: " ++ show o)
      where e = expected test
            o = obtained test

