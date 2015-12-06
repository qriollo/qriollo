
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

module Test.TestQriolloJvm(test) where

import System.Process(readProcess)
import qualified Data.Map as Map(fromList)

import Test.QriolloTestCases(stringProgramTestCases, prelude)
import Test.Testing(testMany)
import Primitive(primMain)
import Reader(readFromStrings)
import QriolloEval(compilePackages, OptionsQ, OptionQ(..))

globalPackage = ["Input"]

jarName = "__Output.jar"

execJava :: IO String
execJava = readProcess "java" ["-jar", jarName] ""

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
           "TestQriolloJvm/stringProgramTestCases !! " ++ show i ++ "\n" ++
           "Programa: " ++ show program ++ "\n" ++
           "Esperado: " ++ show expected ++ "\n" ++
           "Obtenidos: " ++ show obtainedList ++ "\n")

    obtained :: String -> Integer -> IO String 
    obtained program nOptimizationRounds = do
       case readFromStrings [(globalPackage, prelude ++ "\n" ++ program)] of
         Left msg       -> error msg
         Right packages -> do
           mCode <- compilePackages (options nOptimizationRounds) packages 
           case mCode of
             Left msg -> error msg
             Right "" -> do
               result <- execJava
               return result

    options :: Integer -> OptionsQ
    options nOptimizationRounds =
      Map.fromList [
        (OptQ_OptimizationRounds, show nOptimizationRounds),
        (OptQ_CheckInternalInvariants, ""),
        (OptQ_Compile, ""),
        (OptQ_OutputLanguage, "Jvm"),
        (OptQ_OutputFile, jarName),
        (OptQ_JvmOptionsToplevel, "JvmOpt_ToplevelShowAsString")
      ]

test :: IO (Either String ())
test = testN 1

