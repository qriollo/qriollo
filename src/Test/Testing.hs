
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

