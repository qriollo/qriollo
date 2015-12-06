
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

module Test.TestBackendPy(test) where

import Backend.Py(
        compileToPy,
        PyOptions(..), PyOptionsMangling(..), PyOptionsToplevel(..),
    )
import Test.Testing(TestResult, testMany)
import Numeric(showHex)

import ExpressionE
import ExpressionL
import ExpressionK
import Primitive(primMaxFixnum)

--TODO: Update with new output
simpleTestCases :: [(ExprK, String)]
simpleTestCases = []

{--
simpleTestCases :: [(ExprK, String)]
simpleTestCases = [
  (AppK (VarK 0) [],
    "import sys\n" ++
    "return v_0, ()\n"),
  (AppK (VarK 0) [VarK 1], 
    "import sys\n" ++
    "return v_0, (v_1,)\n"),
  (AppK (VarK 0) [VarK 1, VarK 2],
    "import sys\n" ++
    "return v_0, (v_1, v_2)\n"),
  (RecordK [VarK 0] 1 (AppK (VarK 0) []),
    "import sys\n" ++
    "v_1 = (v_0,)\n" ++
    "return v_0, ()\n"),
  (SelectK 2 (VarK 9) 2 (AppK (VarK 0) []),
    "import sys\n" ++
    "v_2 = v_9[2]\n" ++
    "return v_0, ()\n"),
  (LetK [ValueDK 0 [1, 2] (AppK (VarK 1) [])]
        (AppK (VarK 0) [ConstantK (FixnumC 3), ConstantK (FixnumC 4)]),
    "import sys\n" ++
    "def v_0(v_1, v_2):\n" ++
    "  return v_1, ()\n" ++
    "def main():\n" ++
    "  return v_0, (3, 4)\n" ++
    "write = sys.stdout.write\n" ++
    "def top(value):\n" ++
    "  sys.exit(0)\n" ++
    "f, xs = main, ()\n" ++
    "while True:\n" ++
    "  f, xs = f(*xs)\n"
  ),
  (SwitchK (VarK 1) [
     AppK (VarK 0) []
   ],
   "import sys\n" ++
   "def l_0():\n" ++
   "  return v_0, ()\n" ++
   "return (l_0,)[v_1]()\n"
  ),
  (SwitchK (VarK 9) [
     AppK (VarK 0) [],
     AppK (VarK 1) [VarK 2]
   ],
   "import sys\n" ++
   "def l_0():\n" ++
   "  return v_0, ()\n" ++
   "def l_1():\n" ++
   "  return v_1, (v_2,)\n" ++
   "return (l_0, l_1)[v_9]()\n"
  ),
  (PrimitiveK PrimRef [VarK 2] [3] [
     AppK (VarK 0) [VarK 3]
   ],
   "import sys\n" ++
   "v_3 = [v_2]\n" ++
   "return v_0, (v_3,)\n"
  ),
  (PrimitiveK PrimDeref [VarK 2] [3] [
     AppK (VarK 0) [VarK 3]
   ],
   "import sys\n" ++
   "v_3 = v_2[0]\n" ++
   "return v_0, (v_3,)\n"
  ),
  (PrimitiveK PrimAssign [VarK 2, VarK 3] [4] [
     AppK (VarK 0) [VarK 3]
   ],
   "import sys\n" ++
   "v_2[0] = v_3\n" ++
   "v_4 = 0\n" ++
   "return v_0, (v_3,)\n"
  ),
  (PrimitiveK PrimFixnumAdd [VarK 2, VarK 3] [4] [
     AppK (VarK 0) [VarK 3]
   ],
   "import sys\n" ++
   "v_4 = (v_2 + v_3) % 0x" ++ showHex primMaxFixnum "" ++ "\n" ++
   "return v_0, (v_3,)\n"
  ),
  (PrimitiveK PrimFixnumSub [VarK 2, VarK 3] [4] [
     AppK (VarK 0) [VarK 3]
   ],
   "import sys\n" ++
   "v_4 = (v_2 - v_3) % 0x" ++ showHex primMaxFixnum "" ++ "\n" ++
   "return v_0, (v_3,)\n"
  ),
  (PrimitiveK PrimFixnumEq [VarK 2, VarK 3] [] [
     AppK (VarK 0) [VarK 3],
     AppK (VarK 1) [VarK 4]
   ],
   "import sys\n" ++
   "if v_2 == v_3:\n" ++
   "  return v_0, (v_3,)\n" ++
   "else:\n" ++
   "  return v_1, (v_4,)\n"
  ),
  (PrimitiveK PrimFixnumLe [VarK 2, VarK 3] [] [
     AppK (VarK 0) [VarK 3],
     AppK (VarK 1) [VarK 4]
   ],
   "import sys\n" ++
   "if v_2 <= v_3:\n" ++
   "  return v_0, (v_3,)\n" ++
   "else:\n" ++
   "  return v_1, (v_4,)\n"
  ),
  (PrimitiveK PrimBoxed [VarK 2] [] [
     AppK (VarK 0) [VarK 3],
     AppK (VarK 1) [VarK 4]
   ],
   "import sys\n" ++
   "if isinstance(v_2, tuple):\n" ++
   "  return v_0, (v_3,)\n" ++
   "else:\n" ++
   "  return v_1, (v_4,)\n"
  ),
  (PrimitiveK PrimTag [VarK 2] [4] [
     AppK (VarK 1) [VarK 4]
   ],
   "import sys\n" ++
   "if isinstance(v_2, tuple):\n" ++
   "  v_4 = v_2[0]\n" ++
   "else:\n" ++
   "  v_4 = v_2\n" ++
   "return v_1, (v_4,)\n"
  ),
  (PrimitiveK PrimPutChar [VarK 2] [4] [
     AppK (VarK 1) [VarK 4]
   ],
   "import sys\n" ++
   "write(unichr(v_2))\n" ++
   "v_4 = 0\n" ++
   "return v_1, (v_4,)\n"
  ),
  (PrimitiveK PrimPutChar [VarK 2] [] [
     AppK (VarK 1) [VarK 5]
   ],
   "import sys\n" ++
   "write(unichr(v_2))\n" ++
   "return v_1, (v_5,)\n"
  ),
  (PrimitiveK PrimPutChar [ConstantK (CharC 'H')] [] [
     AppK (VarK 1) [VarK 5]
   ],
   "import sys\n" ++
   "write(u\"H\")\n" ++
   "return v_1, (v_5,)\n"
  ),
  (PrimitiveK PrimPutChar [ConstantK (CharC 'H')] [] [
     PrimitiveK PrimPutChar [ConstantK (CharC 'o')] [] [
       PrimitiveK PrimPutChar [ConstantK (CharC 'l')] [] [
         PrimitiveK PrimPutChar [ConstantK (CharC 'a')] [] [
           AppK (VarK 1) [VarK 5]
         ]
       ]
     ]
   ],
   "import sys\n" ++
   "write(u\"Hola\")\n" ++
   "return v_1, (v_5,)\n"
  ),
  (PrimitiveK PrimPutChar [ConstantK (CharC '\x0f')] [] [
     AppK (VarK 1) [VarK 5]
   ],
   "import sys\n" ++
   "write(u\"\\x0f\")\n" ++
   "return v_1, (v_5,)\n"
  ),
  (PrimitiveK PrimPutChar [ConstantK (CharC '\\')] [] [
     AppK (VarK 1) [VarK 5]
   ],
   "import sys\n" ++
   "write(u\"\\\\\")\n" ++
   "return v_1, (v_5,)\n"
  ),
  (PrimitiveK PrimPutChar [ConstantK (CharC '\'')] [] [
     AppK (VarK 1) [VarK 5]
   ],
   "import sys\n" ++
   "write(u\"\\\'\")\n" ++
   "return v_1, (v_5,)\n"
  ),
  (PrimitiveK PrimPutChar [ConstantK (CharC '\"')] [] [
     AppK (VarK 1) [VarK 5]
   ],
   "import sys\n" ++
   "write(u\"\\\"\")\n" ++
   "return v_1, (v_5,)\n"
  ),
  (ForeignK (ForeignSignature
               ForeignLangPy "ff({1}, {2})"
               [ForeignString, ForeignString]
               ForeignString)
     [VarK 2, VarK 3]
     4
     (AppK (VarK 1) [VarK 4]),
   "import sys\n" ++
   "v_4 = string_pi(ff(string_ip(v_2), string_ip(v_3)))\n" ++
   "return v_1, (v_4,)\n"
  ),

  -- sentinel
  (AppK (VarK 0) [],
    "import sys\n" ++
    "return v_0, ()\n")
  ]
--}

testN :: Int -> TestResult
testN 1 = testMany "TestClosure.simpleTestCases" simpleTestCases
    (\ (_, expected)   -> expected)
    (\ (expression, _) -> compileToPy options [] expression)
  where
    options :: PyOptions
    options = PyOptions {
                pyoMangling = PyOpt_TrivialMangling,
                pyoToplevel = PyOpt_ToplevelExit
              }

test :: TestResult
test = mapM_ testN [1]

