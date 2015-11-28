
module Test.TestClosure(test) where

import RegAlloc(allocateRegisters, assignRegisters)
import Test.Testing(TestResult, testMany)

import ExpressionE
import ExpressionL
import ExpressionK

allocateRegistersTestCases :: [(ExprK, ExprK)]
allocateRegistersTestCases = [
  -- Do not spill
    ( RecordK [ConstantK (FixnumC 1)] 2 (retK (VarK 2)),
      RecordK [ConstantK (FixnumC 1)] 2 (retK (VarK 2))
    ),

  -- Do not spill: (most) variables are not live
    ( RecordK [] 1 $
      RecordK [] 2 $
      RecordK [] 3 $
      RecordK [] 4 $
      RecordK [] 5 $
      RecordK [] 6 $
      RecordK [] 7 $
      RecordK [] 8 $
      RecordK [] 9 $
      (retK (VarK 1)),
      RecordK [] 1 $
      RecordK [] 2 $
      RecordK [] 3 $
      RecordK [] 4 $
      RecordK [] 5 $
      RecordK [] 6 $
      RecordK [] 7 $
      RecordK [] 8 $
      RecordK [] 9 $
      (retK (VarK 1))
    ),

  -- Spill
    ( RecordK [] 1 $
      RecordK [] 2 $
      RecordK [] 3 $
      RecordK [] 5 $
      RecordK [] 6 $
      RecordK [] 7 $
      RecordK [VarK 1, VarK 2] 4 $
      RecordK [VarK 5, VarK 6] 8 $
      (retK (VarK 7)),

      RecordK [] 1 $
      RecordK [] 2 $
      RecordK [] 3 $
      RecordK [] 5 $
      RecordK [VarK 1, VarK 2, VarK 5] 9 $
      RecordK [] 6 $
      RecordK [] 7 $
      RecordK [SelK 0 9, SelK 1 9] 4 $
      RecordK [SelK 2 9, VarK 6] 8 $
      (retK (VarK 7))
    ),

    ( RecordK [] 1 $
      RecordK [] 2 $
      RecordK [] 3 $
      RecordK [] 4 $
      RecordK [] 5 $
      RecordK [VarK 1, VarK 2, VarK 3, VarK 4, VarK 5] 6 $
      retK (VarK 6),
      RecordK [] 1 $
      RecordK [] 2 $
      RecordK [] 3 $
      RecordK [VarK 1, VarK 2, VarK 3] 7 $
      RecordK [] 4 $
      RecordK [] 5 $
      RecordK [SelK 0 7, SelK 1 7, SelK 2 7, VarK 4, VarK 5] 6 $
      retK (VarK 6)
    ),

    ( RecordK [] 1 $
      RecordK [] 2 $
      RecordK [] 3 $
      RecordK [] 4 $
      RecordK [] 5 $
      AppK (VarK 1) [VarK 2, VarK 3],
      RecordK [] 1 $
      RecordK [] 2 $
      RecordK [] 3 $
      RecordK [VarK 1, VarK 2, VarK 3] 6 $
      RecordK [] 4 $
      RecordK [] 5 $
      SelectK 0 (VarK 6) 7 $
      SelectK 1 (VarK 6) 8 $
      SelectK 2 (VarK 6) 9 $
      AppK (VarK 7) [VarK 8, VarK 9]
    ),

    ( RecordK [] 1 $
      RecordK [] 2 $
      RecordK [] 3 $
      RecordK [] 4 $
      RecordK [] 5 $
      ForeignK
        (ForeignSignature ForeignLangC "a"
          [ForeignFixnum, ForeignFixnum, ForeignFixnum,
           ForeignFixnum, ForeignFixnum]
          ForeignFixnum)
        [VarK 1, VarK 2, VarK 3, VarK 4, VarK 5] 6 $
      retK (VarK 6),
      RecordK [] 1 $
      RecordK [] 2 $
      RecordK [] 3 $
      RecordK [VarK 1, VarK 2, VarK 3] 7 $
      RecordK [] 4 $
      RecordK [] 5 $
      ForeignK
       (ForeignSignature ForeignLangC "a"
          [ForeignFixnum, ForeignFixnum, ForeignFixnum,
           ForeignFixnum, ForeignFixnum]
          ForeignFixnum)
        [SelK 0 7, SelK 1 7, SelK 2 7, VarK 4, VarK 5] 6 $
      retK (VarK 6)
    ),

  -- sentinel
    (retK (ConstantK (FixnumC 10)), retK (ConstantK (FixnumC 10)))
  ]
  where
    retK val = AppK (LabelK (-1)) [val]

assignRegistersTestCases :: [(ExprK, ExprK)]
assignRegistersTestCases = [
  -- Reuse every result
  (
    RecordK [ConstantK (FixnumC 10)] 10 $
    RecordK [ConstantK (FixnumC 10)] 11 $
    RecordK [ConstantK (FixnumC 10)] 12 $
    retK (VarK 12),
    RecordK [ConstantK (FixnumC 10)] 0 $
    RecordK [ConstantK (FixnumC 10)] 0 $
    RecordK [ConstantK (FixnumC 10)] 0 $
    retK (VarK 0)
  ),

  -- Reuse unused results, keep used results 
  (
    RecordK [ConstantK (FixnumC 20)] 10 $
    RecordK [ConstantK (FixnumC 21)] 11 $
    RecordK [ConstantK (FixnumC 22)] 12 $
    RecordK [VarK 10, VarK 12] 13 $
    retK (VarK 13),
    RecordK [ConstantK (FixnumC 20)] 0 $
    RecordK [ConstantK (FixnumC 21)] 1 $
    RecordK [ConstantK (FixnumC 22)] 1 $
    RecordK [VarK 0, VarK 1] 0 $
    retK (VarK 0)
  ),

  -- Visit escaping functions
  (
    LetK [ValueDK 101 [7, 99, 9]
            (AppK (LabelK 101)
                  [LabelK 101, VarK 99, SelK 11 9])] $
    retK (ConstantK $ FixnumC 3), 
    LetK [ValueDK 101 [0, 1, 2]
            (AppK (LabelK 101)
                  [LabelK 101, VarK 1, SelK 11 2])] $
    retK (ConstantK $ FixnumC 3)
  ),

  -- Visit known functions
  (
    LetK [ValueDK 101 [7, 99, 9]
            (AppK (LabelK 101) [VarK 7, VarK 99, VarK 9])] $
    RecordK [ConstantK (FixnumC 20)] 10 $
    RecordK [ConstantK (FixnumC 21)] 11 $
    RecordK [ConstantK (FixnumC 22)] 12 $
    AppK (LabelK 101) [VarK 10, VarK 11, VarK 12], 

    LetK [ValueDK 101 [0, 1, 2]
            (AppK (LabelK 101) [VarK 0, VarK 1, VarK 2])] $
    RecordK [ConstantK (FixnumC 20)] 0 $
    RecordK [ConstantK (FixnumC 21)] 1 $
    RecordK [ConstantK (FixnumC 22)] 2 $
    AppK (LabelK 101) [VarK 0, VarK 1, VarK 2]
  ),

  -- Known functions: respect order of real arguments when possible
  (
    LetK [ValueDK 101 [7, 99, 9]
            (AppK (LabelK 101) [VarK 7, VarK 99, VarK 9])] $
    RecordK [ConstantK (FixnumC 20)] 10 $
    RecordK [ConstantK (FixnumC 21)] 11 $
    RecordK [ConstantK (FixnumC 22)] 12 $
    AppK (LabelK 101) [VarK 12, VarK 11, VarK 10], 
    LetK [ValueDK 101 [2, 1, 0]
            (AppK (LabelK 101) [VarK 2, VarK 1, VarK 0])] $
    RecordK [ConstantK (FixnumC 20)] 0 $
    RecordK [ConstantK (FixnumC 21)] 1 $
    RecordK [ConstantK (FixnumC 22)] 2 $
    AppK (LabelK 101) [VarK 2, VarK 1, VarK 0]
  ),

  -- Known functions: respect order of real arguments when possible
  (
    LetK [ValueDK 101 [7, 8, 99, 199, 9]
            (AppK (LabelK 101) [VarK 7, VarK 8, VarK 99, VarK 199, VarK 9])] $
    RecordK [ConstantK (FixnumC 20)] 10 $
    RecordK [ConstantK (FixnumC 21)] 11 $
    RecordK [ConstantK (FixnumC 22)] 12 $
    AppK (LabelK 101) [VarK 12, VarK 11, VarK 12, VarK 10, VarK 12], 
    LetK [ValueDK 101 [2, 1, 3, 0, 4]
            (AppK (LabelK 101) [VarK 2, VarK 1, VarK 3, VarK 0, VarK 4])] $
    RecordK [ConstantK (FixnumC 20)] 0 $
    RecordK [ConstantK (FixnumC 21)] 1 $
    RecordK [ConstantK (FixnumC 22)] 2 $
    AppK (LabelK 101) [VarK 2, VarK 1, VarK 2, VarK 0, VarK 2]
  ),

  -- SelectK
  (
    RecordK [ConstantK (FixnumC 10), ConstantK (FixnumC 11)] 10 $
    SelectK 1 (VarK 10) 11 $
    retK (VarK 11),
    RecordK [ConstantK (FixnumC 10), ConstantK (FixnumC 11)] 0 $
    SelectK 1 (VarK 0) 0 $
    retK (VarK 0)
  ),

  -- SwitchK
  (
    RecordK [ConstantK (FixnumC 10), ConstantK (FixnumC 11)] 10 $
    SelectK 1 (VarK 10) 11 $
    SwitchK (VarK 11) [
      retK (VarK 10),
      RecordK [ConstantK (FixnumC 12)] 12 $
      retK (VarK 12)
    ],
    RecordK [ConstantK (FixnumC 10), ConstantK (FixnumC 11)] 0 $
    SelectK 1 (VarK 0) 1 $
    SwitchK (VarK 1) [
      retK (VarK 0),
      RecordK [ConstantK (FixnumC 12)] 0 $
      retK (VarK 0)
    ]
  ),

  -- PrimitiveK
  (
    RecordK [ConstantK (FixnumC 10), ConstantK (FixnumC 11)] 10 $
    RecordK [ConstantK (FixnumC 20), ConstantK (FixnumC 21)] 11 $
    RecordK [ConstantK (FixnumC 30), ConstantK (FixnumC 31)] 12 $
    PrimitiveK PrimFixnumAdd [VarK 10, VarK 12] [] $
    [retK (VarK 10), retK (VarK 11)],
    RecordK [ConstantK (FixnumC 10), ConstantK (FixnumC 11)] 0 $
    RecordK [ConstantK (FixnumC 20), ConstantK (FixnumC 21)] 1 $
    RecordK [ConstantK (FixnumC 30), ConstantK (FixnumC 31)] 2 $
    PrimitiveK PrimFixnumAdd [VarK 0, VarK 2] [] $
    [retK (VarK 0), retK (VarK 1)]
  ),

  -- PrimitiveK
  (
    RecordK [ConstantK (FixnumC 10), ConstantK (FixnumC 11)] 10 $
    RecordK [ConstantK (FixnumC 20), ConstantK (FixnumC 21)] 11 $
    RecordK [ConstantK (FixnumC 30), ConstantK (FixnumC 31)] 12 $
    PrimitiveK PrimFixnumAdd [VarK 10, VarK 12] [13] $
    [retK (VarK 13)],
    RecordK [ConstantK (FixnumC 10), ConstantK (FixnumC 11)] 0 $
    RecordK [ConstantK (FixnumC 20), ConstantK (FixnumC 21)] 1 $
    RecordK [ConstantK (FixnumC 30), ConstantK (FixnumC 31)] 1 $
    PrimitiveK PrimFixnumAdd [VarK 0, VarK 1] [0] $
    [retK (VarK 0)]
  ),

  -- ForeignK
  (
    RecordK [ConstantK (FixnumC 10), ConstantK (FixnumC 11)] 10 $
    RecordK [ConstantK (FixnumC 20), ConstantK (FixnumC 21)] 11 $
    RecordK [ConstantK (FixnumC 30), ConstantK (FixnumC 31)] 12 $
    ForeignK
      (ForeignSignature ForeignLangC "a"
                [ForeignFixnum, ForeignFixnum, ForeignFixnum,
                 ForeignFixnum, ForeignFixnum]
                ForeignFixnum)
      [VarK 11, VarK 10, VarK 12] 13 $
    retK (VarK 10),
    RecordK [ConstantK (FixnumC 10), ConstantK (FixnumC 11)] 0 $
    RecordK [ConstantK (FixnumC 20), ConstantK (FixnumC 21)] 1 $
    RecordK [ConstantK (FixnumC 30), ConstantK (FixnumC 31)] 2 $
    ForeignK
      (ForeignSignature ForeignLangC "a"
                [ForeignFixnum, ForeignFixnum, ForeignFixnum,
                 ForeignFixnum, ForeignFixnum]
                ForeignFixnum)
      [VarK 1, VarK 0, VarK 2] 1 $
    retK (VarK 0)
  ),

  -- Escaping function calls known function
  (
    LetK [
      ValueDK 100 [20, 21]
        (AppK (LabelK 101) [LabelK 100, VarK 20, VarK 21]),
      ValueDK 101 [30, 31, 32]
        (RecordK [SelK 0 30, SelK 1 31, SelK 2 32] 33
          (retK (VarK 33)))
    ] $
    (AppK (LabelK 100) [ConstantK $ FixnumC 10, ConstantK $ FixnumC 11]),

    LetK [
      ValueDK 100 [0, 1]
        (AppK (LabelK 101) [LabelK 100, VarK 0, VarK 1]),
      ValueDK 101 [2, 0, 1]
        (RecordK [SelK 0 2, SelK 1 0, SelK 2 1] 0
          (retK (VarK 0)))
    ] $
    (AppK (LabelK 100) [ConstantK $ FixnumC 10, ConstantK $ FixnumC 11])
  ),

  -- sentinel
  (AppK (LabelK 1) [], AppK (LabelK 1) [])
  ]
  where
    retK val = AppK (LabelK (-1)) [val]

testN :: Int -> TestResult
testN 1 = testMany "TestClosure.allocateRegistersTestCases"
                   allocateRegistersTestCases
  (\ (_, expected)   -> expected)
  (\ (expression, _) -> allocateRegisters 4 expression)
testN 2 = testMany "TestClosure.assignRegistersTestCases"
                   assignRegistersTestCases
  (\ (_, expected)   -> expected)
  (\ (expression, _) -> assignRegisters 6 expression)

test :: TestResult
test = mapM_ testN [1..2]

