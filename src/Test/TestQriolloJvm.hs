
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

