
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

module Test.TestOptim(test) where

import Data.Char(ord)

import ExpressionE
import ExpressionL
import ExpressionK
import Primitive(primMinFixnum, primMaxFixnum)
import Optim(
        OptimOptions(..),
        betaContract, deadCodeElim, etaContract, betaExpand,
        OptimInfo(..)
    )
import Test.Testing(TestResult, testMany)

betaContractCases :: [(ExprK, ExprK)]
betaContractCases = [
  -- Single use of a function
  (LetK [ValueDK 0 [1] (retK (VarK 1))]
        (AppK (VarK 0) [ConstantK $ FixnumC 10]),
   retK (ConstantK $ FixnumC 10)),

  -- Not optimized: function occurring as a variable but not applied
  (LetK [ValueDK 0 [1] (retK (VarK 1))]
        (RecordK [VarK 0] 2 (retK (VarK 2))),
   LetK [ValueDK 0 [1] (retK (VarK 1))]
        (RecordK [VarK 0] 2 (retK (VarK 2)))),

  -- Not optimized: cyclic function
  (LetK [ValueDK 0 [1] $ AppK (VarK 0) [VarK 1]]
        (retK (ConstantK (FixnumC 10))),
   LetK [ValueDK 0 [1] $ AppK (VarK 0) [VarK 1]]
        (retK (ConstantK (FixnumC 10)))),

  -- Optimizes 0 forwards, does not optimize 2 backwards
  (LetK [ValueDK 0 [1] $ AppK (VarK 2) [VarK 1],
         ValueDK 2 [3] $ retK (VarK 3)]
        (AppK (VarK 0) [ConstantK $ FixnumC 10]),
   LetK [ValueDK 2 [3] $ retK (VarK 3)]
        (AppK (VarK 2) [ConstantK $ FixnumC 10])),

  -- Optimizes both 2 and 0 forwards
  (LetK [ValueDK 2 [3] $ retK (VarK 3),
         ValueDK 0 [1] $ AppK (VarK 2) [VarK 1]]
        (AppK (VarK 0) [ConstantK $ FixnumC 10]),
   retK (ConstantK $ FixnumC 10)),

  -- Erase unused declaration
  (LetK [ValueDK 0 [1] $ RecordK [ConstantK $ FixnumC 12] 2 (retK (VarK 2))]
        (retK (ConstantK $ FixnumC 10)),
   retK (ConstantK $ FixnumC 10)),

  -- Erase unused record
  (RecordK [ConstantK $ FixnumC 10, ConstantK $ FixnumC 20] 3 $
   retK (ConstantK $ FixnumC 11),
   retK (ConstantK $ FixnumC 11)),

  -- Do not erase used record
  (RecordK [ConstantK $ FixnumC 10, ConstantK $ FixnumC 20] 3 $
   retK (VarK 3),
   RecordK [ConstantK $ FixnumC 10, ConstantK $ FixnumC 20] 3 $
   retK (VarK 3)),

  -- Erase unused selection
  (RecordK [ConstantK $ FixnumC 10, ConstantK $ FixnumC 20] 3 $
   SelectK 0 (VarK 3) 4 $
   retK (ConstantK $ FixnumC 11),
   RecordK [ConstantK $ FixnumC 10, ConstantK $ FixnumC 20] 3 $
   retK (ConstantK $ FixnumC 11)),

  -- Do not erase used selection
  (SelectK 0 (VarK 3) 4 $
   retK (VarK 4),
   SelectK 0 (VarK 3) 4 $
   retK (VarK 4)),

  -- Erase unused primitive operation that has no side effects
  (PrimitiveK PrimFixnumAdd
              [ConstantK $ FixnumC 10, ConstantK $ FixnumC 20]
              [3] [
       retK (ConstantK $ FixnumC 11)
   ],
   retK (ConstantK $ FixnumC 11)),

  -- Do not erase used primitive operation even if it has no side effects
  (PrimitiveK PrimFixnumAdd
              [ConstantK $ FixnumC 10, VarK 7]
              [3] [
       retK (VarK 3)
   ],
   PrimitiveK PrimFixnumAdd
              [ConstantK $ FixnumC 10, VarK 7]
              [3] [
       retK (VarK 3)
   ]),

  -- Do not erase unused primitive operation when it has side effects
  (PrimitiveK PrimPutChar [ConstantK $ CharC 'a'] [3] [
       retK (VarK 3)
   ],
   PrimitiveK PrimPutChar [ConstantK $ CharC 'a'] [3] [
       retK (VarK 3)
   ]),

  -- But erase the resulting binding when it is not needed
  (PrimitiveK PrimPutChar [ConstantK $ CharC 'a'] [3] [
       retK (ConstantK $ FixnumC 10)
   ],
   PrimitiveK PrimPutChar [ConstantK $ CharC 'a'] [] [
       retK (ConstantK $ FixnumC 10)
   ]),

  -- Do not erase the resulting binding when it is needed
  (PrimitiveK PrimAssign [VarK 2, VarK 3] [4] [
       retK (VarK 4)
   ],
   PrimitiveK PrimAssign [VarK 2, VarK 3] [4] [
       retK (VarK 4)
   ]),

  -- Erase the resulting binding when it is not needed
  (PrimitiveK PrimAssign [VarK 2, VarK 3] [4] [
       retK (VarK 7)
   ],
   PrimitiveK PrimAssign [VarK 2, VarK 3] [] [
       retK (VarK 7)
   ]),

  -- Constant folding: fixnum addition
  (PrimitiveK PrimFixnumAdd
              [ConstantK $ FixnumC 10, ConstantK $ FixnumC 20]
              [3] [
       retK (VarK 3)
   ],
   retK (ConstantK $ FixnumC 30)),

  (PrimitiveK PrimFixnumAdd
              [ConstantK $ FixnumC 0, VarK 3]
              [7] [
       retK (VarK 7)
   ],
   retK (VarK 3)),

  (PrimitiveK PrimFixnumAdd
              [VarK 3, ConstantK $ FixnumC 0]
              [7] [
       retK (VarK 7)
   ],
   retK (VarK 3)),

  -- Constant folding: fixnum subtraction
  (PrimitiveK PrimFixnumSub
              [ConstantK $ FixnumC 30, ConstantK $ FixnumC 14]
              [3] [
       retK (VarK 3)
   ],
   retK (ConstantK $ FixnumC 16)),

  (PrimitiveK PrimFixnumSub
              [VarK 3, ConstantK $ FixnumC 0]
              [7] [
       retK (VarK 7)
   ],
   retK (VarK 3)),

  -- Constant folding: chainings of constant foldings
  (PrimitiveK PrimFixnumAdd
              [ConstantK $ FixnumC 13, ConstantK $ FixnumC 13] [1] [
       PrimitiveK PrimFixnumAdd [VarK 1, VarK 1] [2] [
           retK (VarK 2)
       ]
   ],
   retK (ConstantK $ FixnumC 52)),

  -- Constant folding: fixnum equality
  (PrimitiveK PrimFixnumEq
              [ConstantK $ FixnumC 13, ConstantK $ FixnumC 13] [] [
        retK (ConstantK $ FixnumC 10),
        retK (ConstantK $ FixnumC 11)
   ],
   retK (ConstantK $ FixnumC 10)),

  (PrimitiveK PrimFixnumEq
              [ConstantK $ FixnumC 13, ConstantK $ FixnumC 12] [] [
        retK (ConstantK $ FixnumC 10),
        retK (ConstantK $ FixnumC 11)
   ],
   retK (ConstantK $ FixnumC 11)),

  (PrimitiveK PrimFixnumEq
              [ConstantK $ FixnumC 12, ConstantK $ FixnumC 13] [] [
        retK (ConstantK $ FixnumC 10),
        retK (ConstantK $ FixnumC 11)
   ],
   retK (ConstantK $ FixnumC 11)),

  -- Constant folding: fixnum lesser or equal than
  (PrimitiveK PrimFixnumLe
              [ConstantK $ FixnumC 13, ConstantK $ FixnumC 13] [] [
        retK (ConstantK $ FixnumC 10),
        retK (ConstantK $ FixnumC 11)
   ],
   retK (ConstantK $ FixnumC 10)),

  (PrimitiveK PrimFixnumLe
              [ConstantK $ FixnumC 13, ConstantK $ FixnumC 14] [] [
        retK (ConstantK $ FixnumC 10),
        retK (ConstantK $ FixnumC 11)
   ],
   retK (ConstantK $ FixnumC 10)),

  (PrimitiveK PrimFixnumLe
              [ConstantK $ FixnumC 13, ConstantK $ FixnumC 12] [] [
        retK (ConstantK $ FixnumC 10),
        retK (ConstantK $ FixnumC 11)
   ],
   retK (ConstantK $ FixnumC 11)),

  (PrimitiveK PrimFixnumLe
              [ConstantK $ FixnumC primMinFixnum, VarK 3] [] [
        retK (ConstantK $ FixnumC 10),
        retK (ConstantK $ FixnumC 11)
   ],
   retK (ConstantK $ FixnumC 10)),

  (PrimitiveK PrimFixnumLe
              [VarK 3, ConstantK $ FixnumC primMaxFixnum] [] [
        retK (ConstantK $ FixnumC 10),
        retK (ConstantK $ FixnumC 11)
   ],
   retK (ConstantK $ FixnumC 11)),

  -- Alpha-equivalent branches
  (PrimitiveK PrimFixnumLe
              [VarK 2, VarK 3] [] [
        RecordK [ConstantK (FixnumC 10), ConstantK (FixnumC 11)] 7
                (retK (VarK 7)),
        RecordK [ConstantK (FixnumC 10), ConstantK (FixnumC 11)] 19
                (retK (VarK 19))
   ],
   RecordK [ConstantK (FixnumC 10), ConstantK (FixnumC 11)] 7
           (retK (VarK 7))),

  -- Non alpha-equivalent branches
  (PrimitiveK PrimFixnumLe
              [VarK 2, VarK 3] [] [
        RecordK [ConstantK (FixnumC 4), ConstantK (FixnumC 11)] 7
                (retK (VarK 7)),
        RecordK [ConstantK (FixnumC 10), ConstantK (FixnumC 11)] 19
                (retK (VarK 19))
   ],
   PrimitiveK PrimFixnumLe
              [VarK 2, VarK 3] [] [
        RecordK [ConstantK (FixnumC 4), ConstantK (FixnumC 11)] 7
                (retK (VarK 7)),
        RecordK [ConstantK (FixnumC 10), ConstantK (FixnumC 11)] 19
                (retK (VarK 19))
   ]),

  -- Constant folding: boxed

  -- From constant
  (PrimitiveK PrimBoxed [ConstantK $ FixnumC 13] [] [
        retK (ConstantK $ FixnumC 10),
        retK (ConstantK $ FixnumC 11)
   ],
   retK (ConstantK $ FixnumC 11)),

  -- From well-known record
  (RecordK [ConstantK (FixnumC 40), ConstantK (FixnumC 41)] 2 $
   PrimitiveK PrimBoxed [VarK 2] [] [
        retK (ConstantK $ FixnumC 10),
        retK (ConstantK $ FixnumC 11)
   ],
   RecordK [ConstantK (FixnumC 40), ConstantK (FixnumC 41)] 2 $
   retK (ConstantK $ FixnumC 10)),

  -- From unknown variable
  (PrimitiveK PrimBoxed [VarK 2] [] [
        retK (ConstantK $ FixnumC 10),
        retK (ConstantK $ FixnumC 11)
   ],
   PrimitiveK PrimBoxed [VarK 2] [] [
        retK (ConstantK $ FixnumC 10),
        retK (ConstantK $ FixnumC 11)
   ]),

  -- Constant folding: tagged

  -- From fixnum constant
  (PrimitiveK PrimTag [ConstantK $ FixnumC 13] [2] [
        retK (VarK 2)
   ],
   retK (ConstantK $ FixnumC 13)),

  -- From character constant
  (PrimitiveK PrimTag [ConstantK $ CharC 'A'] [2] [
        retK (VarK 2)
   ],
   retK (ConstantK $ FixnumC $ fromIntegral $ ord 'A')),

  -- From well-known record
  (RecordK [ConstantK $ FixnumC 13, ConstantK $ FixnumC 14] 7 $
   PrimitiveK PrimTag [VarK 7] [2] [
        retK (VarK 2)
   ],
   RecordK [ConstantK $ FixnumC 13, ConstantK $ FixnumC 14] 7 $
   retK (ConstantK $ FixnumC $ 13)),

  -- From unknown variable
  (PrimitiveK PrimTag [VarK 2] [3] [
        retK (VarK 3)
   ],
   PrimitiveK PrimTag [VarK 2] [3] [
        retK (VarK 3)
   ]),

  -- Selection from well-known record
  (RecordK [ConstantK (FixnumC 20), ConstantK (FixnumC 30)] 5 $
   SelectK 0 (VarK 5) 6 $
   retK (VarK 6),
   RecordK [ConstantK (FixnumC 20), ConstantK (FixnumC 30)] 5 $
   retK (ConstantK (FixnumC 20))),

  (RecordK [ConstantK (FixnumC 20), ConstantK (FixnumC 30)] 5 $
   SelectK 1 (VarK 5) 6 $
   retK (VarK 6),
   RecordK [ConstantK (FixnumC 20), ConstantK (FixnumC 30)] 5 $
   retK (ConstantK (FixnumC 30))),

  -- Erase unused arguments
  (LetK [ValueDK 0 [1, 2] (AppK (VarK 1) [ConstantK (FixnumC 10)])] $
   LetK [ValueDK 7 [5] (AppK (VarK 0) [VarK 7, VarK 112])] $
   AppK (VarK 0) [VarK 7, VarK 111],
   LetK [ValueDK 0 [1] (AppK (VarK 1) [ConstantK (FixnumC 10)])] $
   LetK [ValueDK 7 [5] (AppK (VarK 0) [VarK 7])] $
   AppK (VarK 0) [VarK 7]),

  -- Do not erase unused arguments for escaping functions
  (LetK [ValueDK 0 [1, 2] (AppK (VarK 1) [ConstantK (FixnumC 10)])] $
   LetK [ValueDK 7 [5] (AppK (VarK 0) [VarK 7, VarK 112])] $
   AppK (VarK 0) [VarK 0, VarK 111],
   LetK [ValueDK 0 [1, 2] (AppK (VarK 1) [ConstantK (FixnumC 10)])] $
   LetK [ValueDK 7 [5] (AppK (VarK 0) [VarK 7, VarK 112])] $
   AppK (VarK 0) [VarK 0, VarK 111]),

  -- sentinel
  (retK (VarK 0), retK (VarK 0))
  ]

deadCodeElimCases :: [(ExprK, ExprK)]
deadCodeElimCases = [
  -- Simple dead code
  (LetK [ValueDK 0 [1] (AppK (VarK 1) [ConstantK (FixnumC 10)])] $
    retK (ConstantK (FixnumC 11)),
    retK (ConstantK (FixnumC 11))
  ),
  -- Cyclic dead code
  (LetK [ValueDK 0 [1] (AppK (VarK 0) [ConstantK (FixnumC 10)])] $
    retK (ConstantK (FixnumC 11)),
    retK (ConstantK (FixnumC 11))
  ),
  -- sentinel
  (retK (VarK 0), retK (VarK 0))
  ]

etaContractCases :: [(ExprK, ExprK)]
etaContractCases = [
  -- Simple definition
  (LetK [ValueDK 0 [1, 2] (AppK (VarK 3) [VarK 1, VarK 2])] $
   AppK (VarK 0) [ConstantK (FixnumC 10), ConstantK (FixnumC 11)],
   LetK [] $
   AppK (VarK 3) [ConstantK (FixnumC 10), ConstantK (FixnumC 11)]),

  -- Do not eta expand
  (LetK [ValueDK 0 [1, 2] (AppK (VarK 3) [VarK 2, VarK 1])] $
   AppK (VarK 0) [ConstantK (FixnumC 10), ConstantK (FixnumC 11)],
   LetK [ValueDK 0 [1, 2] (AppK (VarK 3) [VarK 2, VarK 1])] $
   AppK (VarK 0) [ConstantK (FixnumC 10), ConstantK (FixnumC 11)]),

  -- Subtitute definition occurring syntactically before
  (LetK [ValueDK 5 [6] (AppK (VarK 0)
                         [ConstantK (FixnumC 7), ConstantK (FixnumC 8)]),
         ValueDK 0 [1, 2] (AppK (VarK 3) [VarK 1, VarK 2])] $
   AppK (VarK 0) [ConstantK (FixnumC 10), ConstantK (FixnumC 11)],

   LetK [ValueDK 5 [6] (AppK (VarK 3)
                         [ConstantK (FixnumC 7), ConstantK (FixnumC 8)])] $
   AppK (VarK 3) [ConstantK (FixnumC 10), ConstantK (FixnumC 11)]),

  -- Uncurrying
  (LetK [ValueDK 0 [1, 2]
          (LetK [ValueDK 3 [4, 5] (retK (ConstantK (FixnumC 10)))] 
                (AppK (VarK 1) [VarK 3]))]
        (AppK (VarK 0) [ConstantK (FixnumC 11)]),
   LetK [ValueDK 0 [7, 8]
          (LetK [ValueDK 9 [10, 11]
                  (AppK (VarK 6) [VarK 7, VarK 8, VarK 9, VarK 10, VarK 11])] 
                (AppK (VarK 7) [VarK 9])),
         ValueDK 6 [1, 2, 3, 4, 5] (retK (ConstantK (FixnumC 10)))]
        (AppK (VarK 0) [ConstantK (FixnumC 11)])),

  -- sentinel
  (retK (VarK 0), retK (VarK 0))
  ]

betaExpandCases :: [(ExprK, ExprK)]
betaExpandCases = [
  (LetK [ValueDK 0 [1] (retK (VarK 1))] $
   LetK [ValueDK 2 [3] (AppK (VarK 0) [ConstantK (FixnumC 12)])] $
     AppK (VarK 0) [ConstantK (FixnumC 13)],

   LetK [ValueDK 0 [1] (retK (VarK 1))] $
   LetK [ValueDK 2 [3] (retK (ConstantK (FixnumC 12)))] $
     (retK (ConstantK (FixnumC 13)))
  ),
  -- sentinel
  (retK (VarK 0), retK (VarK 0))
  ]

testN :: Int -> TestResult
testN 1 = testMany "TestOptim.betaContractCases" betaContractCases
  (\ (_, expected)   -> expected)
  (\ (expression, _) -> osResult $ betaContract expression)
testN 2 = testMany "TestOptim.deadCodeElimCases" deadCodeElimCases
  (\ (_, expected)   -> expected)
  (\ (expression, _) -> osResult $ deadCodeElim expression)
testN 3 = testMany "TestOptim.etaContractCases" etaContractCases
  (\ (_, expected)   -> expected)
  (\ (expression, _) -> osResult $ etaContract expression)
testN 4 = testMany "TestOptim.betaExpandCases" betaExpandCases
  (\ (_, expected)   -> expected)
  (\ (expression, _) -> osResult $ betaExpand OptimizeForTime 1 expression)

test :: TestResult
test = mapM_ testN [1..4]

