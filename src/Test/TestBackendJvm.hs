
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

module Test.TestBackendJvm(test) where

import System.IO(openBinaryFile, IOMode(..), hPutStr, hClose)

import ExpressionE
import ExpressionL
import ExpressionK

import Backend.JvmClass(bytecode)
import Backend.Jvm(compileToJvm, JvmOptions(..), JvmOptionsToplevel(..))

testClass :: String
testClass = compileToJvm
              (JvmOptions { jvoToplevel = JvmOpt_ToplevelExit })
              [] -- pragmas
              "Test" (
              LetK [ValueDK 7 [0, 1] $
                      SwitchK (VarK 0) [
                        retK (ConstantK (FixnumC 2000)),
                        retK (ConstantK (FixnumC 2001)),
                        retK (ConstantK (FixnumC 2002)),
                        retK (ConstantK (FixnumC 2003)),
                        retK (ConstantK (FixnumC 2004)),
                        retK (ConstantK (FixnumC 2005)),
                        retK (ConstantK (FixnumC 2006)),
                        retK (ConstantK (FixnumC 2007)),
                        retK (ConstantK (FixnumC 2008)),
                        retK (ConstantK (FixnumC 2009)),
                        PrimitiveK PrimRef [ConstantK (FixnumC 7)] [1] [
                        PrimitiveK PrimAssign
                               [VarK 1, ConstantK (FixnumC 86400123)] [2] [
                        PrimitiveK PrimDeref [VarK 1] [1] [
                        RecordK [ConstantK (FixnumC 13),
                                 ConstantK (FixnumC 0),
                                 ConstantK (FixnumC 97)] 5 $
                        PrimitiveK PrimFixnumSub
                               [VarK 1, ConstantK (FixnumC 7)] [2] [
                          PrimitiveK PrimFixnumLe
                            [VarK 2, ConstantK (FixnumC 86400117)]
                            []
                            [
                              PrimitiveK PrimTag [VarK 2] [7] [
                                PrimitiveK PrimPutChar
                                           [SelK 2 5] [] [
                                retK (VarK 7)
                              ]]
                            ,
                              retK (ConstantK $ FixnumC 0)
                            ]
                        ]
                        ]]],
                        retK (ConstantK (FixnumC 2011)),
                        retK (ConstantK (FixnumC 2012)),
                        retK (ConstantK (FixnumC 2013)),
                        retK (ConstantK (FixnumC 2014)),
                        retK (ConstantK (FixnumC 2015))
                      ]
                   ] $
                RecordK [ConstantK (FixnumC 10),
                         ConstantK (FixnumC 11)] 0 $
                RecordK [VarK 0] 1 $
                SelectK 0 (VarK 1) 2 $

                SelectK 0 (VarK 2) 3 $
                SelectK 1 (VarK 2) 4 $
                  (AppK (LabelK 7)
                        [VarK 3, VarK 4])
            )
  where
    retK x = AppK (LabelK (-1)) [x]

test :: IO ()
test = writeJarFile "Test" testClass
  where
    writeJarFile :: String -> String -> IO ()
    writeJarFile clsname bytes = do
      h <- openBinaryFile (clsname ++ ".jar") WriteMode
      hPutStr h bytes
      hClose h

