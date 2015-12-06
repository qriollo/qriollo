
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

module Test.TestBackendC(test) where

import System.Exit(ExitCode(..))
import System.Process(readProcessWithExitCode)

import ExpressionE
import ExpressionL
import ExpressionK
import Backend.C(compileToC)

runCommand :: String -> [String] -> IO ExitCode
runCommand cmd args = do
  (code, out, err) <- readProcessWithExitCode cmd args ""
  putStrLn out
  putStrLn err
  return code

mainExpr :: ExprK
mainExpr = LetK [
      ValueDK 10 [2] $
        RecordK [VarK 2] 3 $
        SelectK 0 (VarK 3) 1 $
        SwitchK (VarK 1) [
          retKK (ConstantK $ FixnumC 10),
          retKK (ConstantK $ FixnumC 11),
          PrimitiveK PrimRef [ConstantK $ FixnumC 12] [7] [
            PrimitiveK PrimAssign [VarK 7, ConstantK $ FixnumC 22] [] [
              PrimitiveK PrimDeref [VarK 7] [5] [
                PrimitiveK PrimTag [VarK 5] [5] [
                  RecordK [VarK 5] 5 $
                  PrimitiveK PrimTag [VarK 5] [6] [
                    PrimitiveK PrimBoxed [VarK 6] [] [
                      retKK (ConstantK (FixnumC 1)),
                      PrimitiveK PrimFixnumLe
                                 [
                                   ConstantK (FixnumC 12),
                                   ConstantK (FixnumC 11)
                                 ]
                                 []
                        [
                            retKK (ConstantK (FixnumC 1)),
                            PrimitiveK PrimPutChar
                                       [ConstantK (FixnumC 65)]
                                       []
                              [
                                retKK (ConstantK (FixnumC 100))
                              ]
                        ]
                    ]
                  ]
                ]
              ] 
            ]
          ]
        ]
    ]
    (AppK (LabelK 10) [ConstantK (FixnumC 2)])
  where
    retKK :: ValueK -> ExprK
    retKK val = AppK (LabelK (-1)) [val]

test :: IO ()
test =
  let cCode = compileToC [] mainExpr
   in do
     writeFile "test.c" cCode

     code <- runCommand "gcc" ["-o", "test.bin", "-Wall", "test.c"]
     if code /= ExitSuccess
      then return ()
      else do
        putStrLn "OK!"
        runCommand "./test.bin" []
        return ()

