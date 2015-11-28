
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

