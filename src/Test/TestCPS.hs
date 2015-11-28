
module Test.TestCPS(test) where

import Test.Testing(TestResult, testOK, testError)

import ExpressionE
import ExpressionL
import ExpressionK
import CPS(cps, CpsOptions(..))

simpleTestCases :: [(ExprL, ExprK)]
simpleTestCases = [

    -- Abstraction
    (LamL 0 (VarL 0),
     LetK [
       ValueDK 0 [1, 2] (AppK (VarK 1) [VarK 2])
     ] (retK (VarK 0))),

    -- Application
    (LamL 0 $ AppL (VarL 0) (ConstantL (FixnumC 10)),
     LetK [
       ValueDK 0 [1, 2] (
         LetK [
           ValueDK 3 [4] (AppK (VarK 1) [VarK 4])
         ]
         (AppK (VarK 2) [VarK 3, ConstantK (FixnumC 10)])
       )
     ] (retK (VarK 0))
    ),

    (AppL (LamL 0 $ AppL (VarL 0) (ConstantL (FixnumC 10)))
          (LamL 1 $ VarL 1),
     LetK [
       ValueDK 0 [1] (retK (VarK 1))
     ] $
     LetK [
       ValueDK 2 [3, 4] (
         LetK [
           ValueDK 5 [6] (AppK (VarK 3) [VarK 6])
         ]
         (AppK (VarK 4) [VarK 5, ConstantK (FixnumC 10)])
       )
     ] $
     LetK [
       ValueDK 7 [8, 9] (AppK (VarK 8) [VarK 9])
     ] $
     (AppK (VarK 2) [VarK 0, VarK 7])
    ),

    -- Let with acyclic values
    (LetL [ValueDL 0 (ConstantL (FixnumC 10))]
          (VarL 0), 
     LetK [ValueDK 0 [1] (retK (VarK 1))] $
       LetK [ValueDK 2 [3, 4] (AppK (VarK 3) [VarK 4])] $
         AppK (VarK 2) [VarK 0, ConstantK (FixnumC 10)]),

    (LetL [ ValueDL 0 (ConstantL (FixnumC 10)),
            ValueDL 1 (ConstantL (FixnumC 11)) ]
          (VarL 0),

     LetK [ValueDK 0 [1] (retK (VarK 1))] $
       LetK [ValueDK 2 [3, 4] $
               LetK [ValueDK 5 [6] (AppK (VarK 3) [VarK 6])] $
                 LetK [ValueDK 7 [8, 9] (AppK (VarK 8) [VarK 4])] $
                  (AppK (VarK 7) [VarK 5, ConstantK (FixnumC 11)])] $
         (AppK (VarK 2) [VarK 0, ConstantK (FixnumC 10)])),

    -- Let with acyclic values
    (LetL [ ValueDL 0 (ConstantL (FixnumC 10)),
            ValueDL 1 (ConstantL (FixnumC 11)) ]
          (VarL 1),

     LetK [ValueDK 0 [1] (retK (VarK 1))] $
       LetK [ValueDK 2 [3, 4] $
               LetK [ValueDK 5 [6] (AppK (VarK 3) [VarK 6])] $
                 LetK [ValueDK 7 [8, 9] (AppK (VarK 8) [VarK 9])] $
                  (AppK (VarK 7) [VarK 5, ConstantK (FixnumC 11)])] $
         (AppK (VarK 2) [VarK 0, ConstantK (FixnumC 10)])),

    -- Let with (perhaps cyclic) functions
    (LetL [ ValueDL 9 (LamL 1 $ VarL 1) ]
          (AppL (VarL 9) (ConstantL $ FixnumC 10)),
     LetK [
        ValueDK 0 [1, 2] $ AppK (VarK 1) [VarK 2]
     ] $
     LetK [
        ValueDK 3 [4] (retK (VarK 4))
     ] $
     AppK (VarK 0) [VarK 3, ConstantK (FixnumC 10)]),

    -- Nullary records
    (RecordL [], retK (ConstantK (FixnumC 0))),

    -- Records
    (RecordL [ConstantL (FixnumC 10)],
     RecordK [ConstantK (FixnumC 10)] 0 (retK (VarK 0))),

    (RecordL [
       RecordL [ConstantL (FixnumC 10)],
       RecordL [ConstantL (FixnumC 11)],
       RecordL [ConstantL (FixnumC 12)]
     ],
     RecordK [ConstantK (FixnumC 10)] 0 $
     RecordK [ConstantK (FixnumC 11)] 1 $
     RecordK [ConstantK (FixnumC 12)] 2 $
     RecordK [VarK 0, VarK 1, VarK 2] 3 $
     retK (VarK 3)),

    -- Select
    (SelectL 1
       (RecordL [
          ConstantL (FixnumC 10),
          ConstantL (FixnumC 11)
         ]),
     RecordK [
         ConstantK (FixnumC 10),
         ConstantK (FixnumC 11)
      ] 0 $
     SelectK 1 (VarK 0) 1 $
     retK (VarK 1)),

    -- Primitive operation with a single branch
    (PrimitiveL PrimFixnumAdd [
       ConstantL (FixnumC 1),
       ConstantL (FixnumC 2)
     ],
     PrimitiveK PrimFixnumAdd [
       ConstantK (FixnumC 1),
       ConstantK (FixnumC 2)
     ] [0] [retK (VarK 0)]
    ),

    (PrimitiveL PrimFixnumAdd [
       PrimitiveL PrimFixnumAdd [
         ConstantL (FixnumC 1),
         ConstantL (FixnumC 2)
       ],
       PrimitiveL PrimFixnumAdd [
         ConstantL (FixnumC 3),
         ConstantL (FixnumC 4)
       ]
     ],
     PrimitiveK PrimFixnumAdd [
          ConstantK (FixnumC 1),
          ConstantK (FixnumC 2)
        ] [0] [
          PrimitiveK PrimFixnumAdd [
            ConstantK (FixnumC 3),
            ConstantK (FixnumC 4)
          ] [1] [
            PrimitiveK PrimFixnumAdd [
              VarK 0,
              VarK 1
            ] [2] [retK (VarK 2)]
          ]
        ]
    ),

    -- Primitive operation with two branches
    (PrimitiveL PrimFixnumEq [
       ConstantL (FixnumC 10),
       ConstantL (FixnumC 11)
     ],
     LetK [
       ValueDK 0 [1] (retK (VarK 1))
     ] $
     PrimitiveK PrimFixnumEq [
         ConstantK (FixnumC 10),
         ConstantK (FixnumC 11)
     ] [] [
       AppK (VarK 0) [ConstantK (FixnumC 0)],
       AppK (VarK 0) [ConstantK (FixnumC 1)]
     ]
    ),

    -- Foreign operation
    (ForeignL (ForeignSignature ForeignLangC
                "add_int" [ForeignFixnum, ForeignFixnum] ForeignFixnum)
     [
       ConstantL (FixnumC 10),
       ConstantL (FixnumC 11)
     ],
     ForeignK (ForeignSignature ForeignLangC
                "add_int" [ForeignFixnum, ForeignFixnum] ForeignFixnum)
     [
       ConstantK (FixnumC 10),
       ConstantK (FixnumC 11)
     ] 0 (retK (VarK 0))
    ),

    -- Match: one branch without alternative
    (LamL 9 $ MatchL (MatchLSpansConstructors [TaggedCR 1]) (VarL 9) [
       MatchBranchL (DataConstructor (TaggedCR 1))
                    (ConstantL $ FixnumC 10)
     ] Nothing,
     LetK [ValueDK 0 [1, 2] $
       AppK (VarK 1) [
          ConstantK (FixnumC 10)
       ]
     ] (retK (VarK 0))
    ),

    -- Match: no branches with alternative
    (LamL 9 $ MatchL (MatchLSpansConstructors [TaggedCR 1]) (VarL 9) [
     ] (Just (ConstantL $ FixnumC 10)),
     LetK [ValueDK 0 [1, 2] $
       AppK (VarK 1) [
          ConstantK (FixnumC 10)
       ]
     ] (retK (VarK 0))
    ),

    -- Match: branches with Untagged constructor
    (LamL 9 $ MatchL (MatchLSpansConstructors [UntaggedCR]) (VarL 9) [
       MatchBranchL (DataConstructor UntaggedCR)
                    (ConstantL $ FixnumC 10)
     ] Nothing,
     LetK [ValueDK 0 [1, 2] $
       AppK (VarK 1) [
          ConstantK (FixnumC 10)
       ]
     ] (retK (VarK 0))
    ),

    -- Match: linear search, without default case
    (LamL 9 $ MatchL (MatchLSpansConstructors [TaggedCR 20, TaggedCR 21])
                     (VarL 9) [
       MatchBranchL (DataConstructor (TaggedCR 20))
                    (ConstantL $ FixnumC 10),
       MatchBranchL (DataConstructor (TaggedCR 21))
                    (ConstantL $ FixnumC 11)
     ] Nothing,
     LetK [ValueDK 0 [1, 2] $
         LetK [ValueDK 3 [4] (AppK (VarK 1) [VarK 4])]
              (PrimitiveK PrimTag [VarK 2] [5] [
                   PrimitiveK PrimFixnumEq
                     [VarK 5, ConstantK (FixnumC 20)] []
                     [
                       -- tag = 20
                       AppK (VarK 3) [ConstantK (FixnumC 10)],
                       -- tag != 20
                       AppK (VarK 3) [ConstantK (FixnumC 11)]
                     ]
              ])
     ] (retK (VarK 0))
    ),

    -- Match: linear search, with default case
    (LamL 9 $ MatchL (MatchLSpansConstructors [TaggedCR 20, TaggedCR 21])
                     (VarL 9) [
       MatchBranchL (DataConstructor (TaggedCR 20))
                    (ConstantL $ FixnumC 10),
       MatchBranchL (DataConstructor (TaggedCR 21))
                    (ConstantL $ FixnumC 11)
     ] (Just (ConstantL $ FixnumC 12)),
     LetK [ValueDK 0 [1, 2] $
         LetK [
                 ValueDK 3 [4] (AppK (VarK 1) [VarK 4]),
                 ValueDK 5 [6] (AppK (VarK 6) [ConstantK (FixnumC 12)])
              ]
              (PrimitiveK PrimTag [VarK 2] [7] [
                   PrimitiveK PrimFixnumEq
                     [VarK 7, ConstantK (FixnumC 20)] []
                     [
                       -- tag = 20
                       AppK (VarK 3) [ConstantK (FixnumC 10)],
                       -- tag != 20
                       PrimitiveK PrimFixnumEq
                         [VarK 7, ConstantK (FixnumC 21)] []
                         [
                           -- tag == 21
                           AppK (VarK 3) [ConstantK (FixnumC 11)],
                           -- tag != 21
                           AppK (VarK 5) [VarK 3]
                         ]
                     ]
              ])
     ] (retK (VarK 0))
    ),

    -- Match: switch, without default case
    (LamL 9 $ MatchL (MatchLSpansConstructors [
                          TaggedCR 20,
                          TaggedCR 21,
                          TaggedCR 22,
                          TaggedCR 23,
                          TaggedCR 24,
                          TaggedCR 25,
                          TaggedCR 26,
                          TaggedCR 27
                      ]) (VarL 9) [
       MatchBranchL (DataConstructor (TaggedCR 20))
                    (ConstantL $ FixnumC 10),
       MatchBranchL (DataConstructor (TaggedCR 21))
                    (ConstantL $ FixnumC 11),
       MatchBranchL (DataConstructor (TaggedCR 22))
                    (ConstantL $ FixnumC 12),
       MatchBranchL (DataConstructor (TaggedCR 23))
                    (ConstantL $ FixnumC 13)
     ] Nothing,
     LetK [ValueDK 0 [1, 2] $
         LetK [ ValueDK 3 [4] (AppK (VarK 1) [VarK 4]) ] $
           PrimitiveK PrimTag [VarK 2] [5] [
             PrimitiveK PrimFixnumSub [VarK 5, ConstantK (FixnumC 20)] [6] [
               SwitchK (VarK 6) [
                 AppK (VarK 3) [ConstantK (FixnumC 10)],
                 AppK (VarK 3) [ConstantK (FixnumC 11)],
                 AppK (VarK 3) [ConstantK (FixnumC 12)],
                 AppK (VarK 3) [ConstantK (FixnumC 13)]
               ]
             ]
           ]
     ] (retK (VarK 0))
    ),

    -- Match: switch with holes, without default case
    (LamL 9 $ MatchL (MatchLSpansConstructors [
                          TaggedCR 20,
                          TaggedCR 21,
                          TaggedCR 22,
                          TaggedCR 23,
                          TaggedCR 24,
                          TaggedCR 25,
                          TaggedCR 26,
                          TaggedCR 27
                      ]) (VarL 9) [
       MatchBranchL (DataConstructor (TaggedCR 20))
                    (ConstantL $ FixnumC 10),
       MatchBranchL (DataConstructor (TaggedCR 23))
                    (ConstantL $ FixnumC 11),
       MatchBranchL (DataConstructor (TaggedCR 25))
                    (ConstantL $ FixnumC 12),
       MatchBranchL (DataConstructor (TaggedCR 27))
                    (ConstantL $ FixnumC 13)
     ] Nothing,
     LetK [ValueDK 0 [1, 2] $
         LetK [ ValueDK 3 [4] (AppK (VarK 1) [VarK 4]) ] $
           PrimitiveK PrimTag [VarK 2] [5] [
             PrimitiveK PrimFixnumSub [VarK 5, ConstantK (FixnumC 20)] [6] [
               SwitchK (VarK 6) [
                 AppK (VarK 3) [ConstantK (FixnumC 10)],
                 AppK (VarK 3) [ConstantK (FixnumC 0)], -- hole
                 AppK (VarK 3) [ConstantK (FixnumC 0)], -- hole
                 AppK (VarK 3) [ConstantK (FixnumC 11)],
                 AppK (VarK 3) [ConstantK (FixnumC 0)], -- hole
                 AppK (VarK 3) [ConstantK (FixnumC 12)],
                 AppK (VarK 3) [ConstantK (FixnumC 0)], -- hole
                 AppK (VarK 3) [ConstantK (FixnumC 13)]
               ]
             ]
           ]
     ] (retK (VarK 0))
    ),

    -- Match: switch with default case
    (LamL 9 $ MatchL (MatchLSpansConstructors [
                          TaggedCR 20,
                          TaggedCR 21,
                          TaggedCR 22,
                          TaggedCR 23,
                          TaggedCR 24,
                          TaggedCR 25,
                          TaggedCR 26,
                          TaggedCR 27
                      ]) (VarL 9) [
       MatchBranchL (DataConstructor (TaggedCR 20))
                    (ConstantL $ FixnumC 10),
       MatchBranchL (DataConstructor (TaggedCR 21))
                    (ConstantL $ FixnumC 11),
       MatchBranchL (DataConstructor (TaggedCR 22))
                    (ConstantL $ FixnumC 12),
       MatchBranchL (DataConstructor (TaggedCR 23))
                    (ConstantL $ FixnumC 13)
     ] (Just (ConstantL $ FixnumC 50)),
     LetK [ValueDK 0 [1, 2] $
         LetK [
                ValueDK 3 [4] (AppK (VarK 1) [VarK 4]),
                ValueDK 5 [6] (AppK (VarK 6) [ConstantK $ FixnumC 50])
              ] $
           PrimitiveK PrimTag [VarK 2] [7] [
             PrimitiveK PrimFixnumLe [ConstantK (FixnumC 20), VarK 7] [] [
               PrimitiveK PrimFixnumLe [VarK 7, ConstantK (FixnumC 23)] [] [
                 PrimitiveK PrimFixnumSub
                            [VarK 7, ConstantK (FixnumC 20)] [8] [
                   SwitchK (VarK 8) [
                     AppK (VarK 3) [ConstantK (FixnumC 10)],
                     AppK (VarK 3) [ConstantK (FixnumC 11)],
                     AppK (VarK 3) [ConstantK (FixnumC 12)],
                     AppK (VarK 3) [ConstantK (FixnumC 13)]
                   ]
                 ],
                 AppK (VarK 5) [VarK 3]
               ],
               AppK (VarK 5) [VarK 3]
             ]
           ]
     ] (retK (VarK 0))
    ),

    -- Match: switch with holes, with default case
    (LamL 9 $ MatchL (MatchLSpansConstructors [
                          TaggedCR 20,
                          TaggedCR 21,
                          TaggedCR 22,
                          TaggedCR 23,
                          TaggedCR 24,
                          TaggedCR 25,
                          TaggedCR 26,
                          TaggedCR 27
                      ]) (VarL 9) [
       MatchBranchL (DataConstructor (TaggedCR 20))
                    (ConstantL $ FixnumC 10),
       MatchBranchL (DataConstructor (TaggedCR 23))
                    (ConstantL $ FixnumC 11),
       MatchBranchL (DataConstructor (TaggedCR 25))
                    (ConstantL $ FixnumC 12),
       MatchBranchL (DataConstructor (TaggedCR 27))
                    (ConstantL $ FixnumC 13)
     ] (Just (ConstantL $ FixnumC 50)),
     LetK [ValueDK 0 [1, 2] $
         LetK [
                ValueDK 3 [4] (AppK (VarK 1) [VarK 4]),
                ValueDK 5 [6] (AppK (VarK 6) [ConstantK $ FixnumC 50])
              ] $
           PrimitiveK PrimTag [VarK 2] [7] [
             PrimitiveK PrimFixnumLe [ConstantK (FixnumC 20), VarK 7] [] [
               PrimitiveK PrimFixnumLe [VarK 7, ConstantK (FixnumC 27)] [] [
                 PrimitiveK PrimFixnumSub
                            [VarK 7, ConstantK (FixnumC 20)] [8] [
                   SwitchK (VarK 8) [
                     AppK (VarK 3) [ConstantK (FixnumC 10)],
                     AppK (VarK 5) [VarK 3], -- hole
                     AppK (VarK 5) [VarK 3], -- hole
                     AppK (VarK 3) [ConstantK (FixnumC 11)],
                     AppK (VarK 5) [VarK 3], -- hole
                     AppK (VarK 3) [ConstantK (FixnumC 12)],
                     AppK (VarK 5) [VarK 3], -- hole
                     AppK (VarK 3) [ConstantK (FixnumC 13)]
                   ]
                 ],
                 AppK (VarK 5) [VarK 3]
               ],
               AppK (VarK 5) [VarK 3]
             ]
           ]
     ] (retK (VarK 0))
    ),

    -- Match: binary search, without default case
    (LamL 9 $ MatchL (MatchLSpansConstructors [
                                TaggedCR 20,
                                TaggedCR 21,
                                TaggedCR 22,
                                TaggedCR 23,
                                TaggedCR 90,
                                TaggedCR 91,
                                TaggedCR 92,
                                TaggedCR 93
                      ]) (VarL 9) [
       MatchBranchL (DataConstructor (ConstantCR 20))
                    (ConstantL $ FixnumC 10),
       MatchBranchL (DataConstructor (ConstantCR 21))
                    (ConstantL $ FixnumC 11),
       MatchBranchL (DataConstructor (ConstantCR 22))
                    (ConstantL $ FixnumC 12),
       MatchBranchL (DataConstructor (ConstantCR 90))
                    (ConstantL $ FixnumC 80),
       MatchBranchL (DataConstructor (ConstantCR 91))
                    (ConstantL $ FixnumC 81),
       MatchBranchL (DataConstructor (ConstantCR 92))
                    (ConstantL $ FixnumC 82),
       MatchBranchL (DataConstructor (ConstantCR 93))
                    (ConstantL $ FixnumC 83)
     ] Nothing,
     LetK [ValueDK 0 [1, 2] $
         LetK [
                ValueDK 3 [4] (AppK (VarK 1) [VarK 4])
              ] $
           PrimitiveK PrimTag [VarK 2] [5] [
             PrimitiveK PrimFixnumLe [ConstantK (FixnumC 90), VarK 5] [] [
               PrimitiveK PrimFixnumSub [VarK 5, ConstantK (FixnumC 90)] [6] [
                 SwitchK (VarK 6) [
                   AppK (VarK 3) [ConstantK (FixnumC 80)],
                   AppK (VarK 3) [ConstantK (FixnumC 81)],
                   AppK (VarK 3) [ConstantK (FixnumC 82)],
                   AppK (VarK 3) [ConstantK (FixnumC 83)]
                 ]
               ],
               PrimitiveK PrimFixnumEq [VarK 5, ConstantK (FixnumC 20)] [] [
                 AppK (VarK 3) [ConstantK (FixnumC 10)],
                 PrimitiveK PrimFixnumEq [VarK 5, ConstantK (FixnumC 21)] [] [
                   AppK (VarK 3) [ConstantK (FixnumC 11)],
                   AppK (VarK 3) [ConstantK (FixnumC 12)]
                 ]
               ]
             ]
           ]
     ] (retK (VarK 0))
    ),

    -- Match: binary search, with default case
    (LamL 9 $ MatchL (MatchLSpansConstructors [
                                TaggedCR 20,
                                TaggedCR 21,
                                TaggedCR 22,
                                TaggedCR 23,
                                TaggedCR 90,
                                TaggedCR 91,
                                TaggedCR 92,
                                TaggedCR 93
                      ]) (VarL 9) [
       MatchBranchL (DataConstructor (ConstantCR 20))
                    (ConstantL $ FixnumC 10),
       MatchBranchL (DataConstructor (ConstantCR 21))
                    (ConstantL $ FixnumC 11),
       MatchBranchL (DataConstructor (ConstantCR 22))
                    (ConstantL $ FixnumC 12),
       MatchBranchL (DataConstructor (ConstantCR 90))
                    (ConstantL $ FixnumC 80),
       MatchBranchL (DataConstructor (ConstantCR 91))
                    (ConstantL $ FixnumC 81),
       MatchBranchL (DataConstructor (ConstantCR 92))
                    (ConstantL $ FixnumC 82),
       MatchBranchL (DataConstructor (ConstantCR 93))
                    (ConstantL $ FixnumC 83)
     ] (Just (ConstantL $ FixnumC 55)),
     LetK [ValueDK 0 [1, 2] $
         LetK [
                ValueDK 3 [4] (AppK (VarK 1) [VarK 4]),
                ValueDK 5 [6] (AppK (VarK 6) [ConstantK $ FixnumC 55])
              ] $
           PrimitiveK PrimTag [VarK 2] [7] [
             PrimitiveK PrimFixnumLe
                        [ConstantK (FixnumC 90), VarK 7] [] [
               -- Unfortunately the same test is done twice:
               PrimitiveK PrimFixnumLe
                          [ConstantK (FixnumC 90), VarK 7] [] [
                 PrimitiveK PrimFixnumLe
                            [VarK 7, ConstantK (FixnumC 93)] [] [
                   PrimitiveK PrimFixnumSub
                              [VarK 7, ConstantK (FixnumC 90)]
                              [8] [
                     SwitchK (VarK 8) [
                       AppK (VarK 3) [ConstantK (FixnumC 80)],
                       AppK (VarK 3) [ConstantK (FixnumC 81)],
                       AppK (VarK 3) [ConstantK (FixnumC 82)],
                       AppK (VarK 3) [ConstantK (FixnumC 83)]
                     ]
                   ],
                   AppK (VarK 5) [VarK 3]
                 ],
                 AppK (VarK 5) [VarK 3]
               ],
               PrimitiveK PrimFixnumEq
                          [VarK 7, ConstantK (FixnumC 20)] [] [
                 AppK (VarK 3) [ConstantK (FixnumC 10)],
                 PrimitiveK PrimFixnumEq
                            [VarK 7, ConstantK (FixnumC 21)] [] [
                   AppK (VarK 3) [ConstantK (FixnumC 11)],
                   PrimitiveK PrimFixnumEq
                              [VarK 7, ConstantK (FixnumC 22)] [] [
                     AppK (VarK 3) [ConstantK (FixnumC 12)],
                     AppK (VarK 5) [VarK 3]
                   ]
                 ]
               ]
             ]
           ]
     ] (retK (VarK 0))
    ),

    -- Match: safe untagged, without default case,
    --        including the safe untagged constructor
    (LamL 9 $ MatchL (MatchLSpansConstructors [
                                ConstantCR 20,
                                ConstantCR 21,
                                SafeUntaggedCR
                      ]) (VarL 9) [
                MatchBranchL (DataConstructor (ConstantCR 20))
                             (ConstantL $ FixnumC 30),
                MatchBranchL (DataConstructor SafeUntaggedCR)
                             (ConstantL $ FixnumC 40)
              ] Nothing,
     LetK [ValueDK 0 [1, 2] $
           LetK [ValueDK 3 [4] (AppK (VarK 1) [VarK 4])] $
           PrimitiveK PrimBoxed [VarK 2] [] [
               -- record => the SafeUntaggedCR constructor
               AppK (VarK 3) [ConstantK $ FixnumC 40],
               -- constant => the remaining constructors
               PrimitiveK PrimTag [VarK 2] [5] [
                 AppK (VarK 3) [ConstantK $ FixnumC 30]
               ]
           ]
     ] (retK (VarK 0))
    ),

    -- Match: safe untagged, with default case,
    --        including the safe untagged constructor
    (LamL 9 $ MatchL (MatchLSpansConstructors [
                                ConstantCR 20,
                                ConstantCR 21,
                                SafeUntaggedCR
                      ]) (VarL 9) [
                MatchBranchL (DataConstructor (ConstantCR 20))
                             (ConstantL $ FixnumC 30),
                MatchBranchL (DataConstructor SafeUntaggedCR)
                             (ConstantL $ FixnumC 40)
              ] (Just (ConstantL $ FixnumC 50)),
     LetK [ValueDK 0 [1, 2] $
           LetK [
                   ValueDK 3 [4] (AppK (VarK 1) [VarK 4]),
                   ValueDK 5 [6] (AppK (VarK 6) [ConstantK $ FixnumC 50])
                ] $
           PrimitiveK PrimBoxed [VarK 2] [] [
               -- record => the SafeUntaggedCR constructor
               AppK (VarK 3) [ConstantK $ FixnumC 40],
               -- constant => the remaining constructors
               PrimitiveK PrimTag [VarK 2] [7] [
                 PrimitiveK PrimFixnumEq [VarK 7, ConstantK (FixnumC 20)]
                            [] [
                     AppK (VarK 3) [ConstantK $ FixnumC 30],
                     AppK (VarK 5) [VarK 3]
                 ]
               ]
           ]
     ] (retK (VarK 0))
    ),

    -- Match: safe untagged, with default case,
    --        NOT including the safe untagged constructor
    (LamL 9 $ MatchL (MatchLSpansConstructors [
                                ConstantCR 20,
                                ConstantCR 21,
                                SafeUntaggedCR
                      ]) (VarL 9) [
                MatchBranchL (DataConstructor (ConstantCR 20))
                             (ConstantL $ FixnumC 30)
              ] (Just (ConstantL $ FixnumC 50)),
     LetK [ValueDK 0 [1, 2] $
           LetK [
                   ValueDK 3 [4] (AppK (VarK 1) [VarK 4]),
                   ValueDK 5 [6] (AppK (VarK 6) [ConstantK $ FixnumC 50])
                ] $
           PrimitiveK PrimBoxed [VarK 2] [] [
               -- record => the SafeUntaggedCR constructor
               AppK (VarK 5) [VarK 3],
               -- constant => the remaining constructors
               PrimitiveK PrimTag [VarK 2] [7] [
                 PrimitiveK PrimFixnumEq [VarK 7, ConstantK (FixnumC 20)]
                            [] [
                     AppK (VarK 3) [ConstantK $ FixnumC 30],
                     AppK (VarK 5) [VarK 3]
                 ]
               ]
           ]
     ] (retK (VarK 0))
    ),

    -- Mutually recursive values (compiled as references)
    (LetL [ValueDL 0 (VarL 1),
           ValueDL 1 (VarL 0)]
          (VarL 0),
     -- Declare references for 0 and 1
     PrimitiveK PrimRef [ConstantK $ FixnumC 0] [0] [
       PrimitiveK PrimRef [ConstantK $ FixnumC 0] [1] [
         LetK [] (
           -- Give value to 0 by dereferencing 1
           PrimitiveK PrimDeref [VarK 1] [5] [
             PrimitiveK PrimAssign [VarK 0, VarK 5] [6] [
             -- Give value to 1 by dereferencing 0
               PrimitiveK PrimDeref [VarK 0] [3] [
                 PrimitiveK PrimAssign [VarK 1, VarK 3] [4] [
                   -- Evaluate and return variable 0
                   PrimitiveK PrimDeref [VarK 0] [2] [
                     retK (VarK 2)
                   ]
                 ]
               ]
             ]
           ]
         )
       ]
     ]),

    -- sentinel
    (ConstantL (FixnumC 10), retK (ConstantK (FixnumC 10)))
  ]

testN :: Int -> TestResult
testN 1 = rec 0 simpleTestCases
  where
    rec _ [] = testOK
    rec i ((expression, expected):ts)
      | obtained == expected = rec (i + 1) ts
      | otherwise =
        testError ("\nFallo el test " ++
                   "(TestCPS.simpleTestCases !! " ++ show i ++ ")" ++
                   "\nAl convertir a CPS: " ++ show expression ++
                   "\nEsperado: " ++ show expected ++
                   "\nObtenido: " ++ show obtained)
      where obtained :: ExprK
            obtained =
              case cps AllowRecursionOnData expression of
                Left msg -> error ("No se puede convertir a CPS\n" ++ msg)
                Right x  -> x

test :: TestResult
test = mapM_ testN [1]

