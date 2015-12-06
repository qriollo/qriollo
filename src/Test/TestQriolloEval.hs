
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

module Test.TestQriolloEval(test) where

import Test.QriolloTestCases(stringProgramTestCases, prelude)
import Test.Testing(testMany)

import qualified Data.Map as Map(fromList)

import Primitive(primMain)
import QriolloEval(evalStringAsString, OptionsQ, OptionQ(..))

testN :: Int -> IO (Either String ())
testN 1 = rec 0 stringProgramTestCases
  where
    rec :: Integer -> [(String, String)] -> IO (Either String ())
    rec _ [] = return $ Right ()
    rec i ((program, expected) : tests) = do
      obtainedList <- mapM (obtained program) [0, 1, 5]
      if all (== expected) obtainedList
       then rec (i + 1) tests
       else
         return $ Left (
           "Falló el test " ++
           "TestQriolloEval/stringProgramTestCases !! " ++ show i ++ "\n" ++
           "Programa: " ++ show program ++ "\n" ++
           "Esperado: " ++ show expected ++ "\n" ++
           "Obtenidos: " ++ show obtainedList ++ "\n")

    obtained :: String -> Integer -> IO String 
    obtained program nOptimizationRounds =
       evalStringAsString (optionsOptimize nOptimizationRounds)
                          primMain
                          (prelude ++ "\n" ++ program)

    optionsOptimize :: Integer -> OptionsQ
    optionsOptimize nOptimizationRounds =
      Map.fromList [
        (OptQ_OptimizationRounds, show nOptimizationRounds),
        (OptQ_CheckInternalInvariants, "")
      ]

test :: IO (Either String ())
test = testN 1

