
module Test.TestAll where

import Control.Applicative((<$>))

import qualified Test.TestParser
import qualified Test.TestUnify
import qualified Test.TestInfer
import qualified Test.TestPrecompiler
import qualified Test.TestCPS
import qualified Test.TestDeps
import qualified Test.TestEval
import qualified Test.TestOptim
import qualified Test.TestClosure
import qualified Test.TestCompress
import qualified Test.TestBackendPy
import qualified Test.TestQriolloEval
import qualified Test.TestQriolloPy

test :: IO String
test = do
    putStrLn "Probando: Analizador sintáctico..."
    checkRight Test.TestParser.test
    putStrLn "Probando: Algoritmo de unificación..."
    checkRight Test.TestUnify.test
    putStrLn "Probando: Inferidor de tipos..."
    checkRight Test.TestInfer.test
    putStrLn "Probando: Precompilador desazucarador..."
    checkRight Test.TestPrecompiler.test
    putStrLn "Probando: Conversor a CPS..."
    checkRight Test.TestCPS.test
    putStrLn "Probando: Analizador de dependencias..."
    checkRight Test.TestDeps.test
    putStrLn "Probando: Intérprete..."
    checkRight =<< Test.TestEval.test
    putStrLn "Probando: Optimizador..."
    checkRight Test.TestOptim.test
    putStrLn "Probando: Conversor de clausuras..."
    checkRight Test.TestClosure.test
    putStrLn "Probando: Compresor..."
    checkRight Test.TestCompress.test
    putStrLn "Probando: Compilador a Python... (OJO: tests incompletos)"
    checkRight Test.TestBackendPy.test
    {-
    putStrLn "Probando: Tests intensivos para el intérprete..."
    checkRight =<< Test.TestQriolloEval.test
    putStrLn "Probando: Tests intensivos para el compilador a Python..."
    checkRight =<< Test.TestQriolloPy.test
    -}
    return "OK"

  where
    checkRight :: Either String b -> IO ()
    checkRight (Left msg) = fail msg
    checkRight (Right _)  = return ()

