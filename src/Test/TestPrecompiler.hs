
module Test.TestPrecompiler(test) where

import Data.Map as Map(Map, empty, lookup, insert)

import Test.Testing(TestResult, testOK, testError)

import ExpressionE
import ExpressionL
import Primitive(
        primPackage, primTFixnum, primReferenceNew, primReferenceDeref,
        primTFunction, primTChar, primTTuple,
    )
import Precompiler(precompile)

globalPackage :: PackageName
globalPackage = ["Input"]

----

qualifyGlobally :: Id -> QualifId
qualifyGlobally = QualifId globalPackage

qualifiedVersion :: (QualifId -> a) -> Id -> a
qualifiedVersion f = f . qualifyGlobally

varE                     = qualifiedVersion naVarE
constructorE             = qualifiedVersion naConstructorE
varT x                   = foldl naAppT (qualifiedVersion naVarT x)
constructorT x           = foldl naAppT (qualifiedVersion naConstructorT x)
valueD                   = qualifiedVersion naValueD
classD cls typ           = naClassD (qualifyGlobally cls) (qualifyGlobally typ)
instanceD                = qualifiedVersion naInstanceD
lamE                     = qualifiedVersion naLamE
typeD a                  = qualifiedVersion naTypeD a . map qualifyGlobally
datatypeD a              = qualifiedVersion naDatatypeD a . map qualifyGlobally
varP                     = qualifiedVersion naVarP
constructorP             = qualifiedVersion naConstructorP
typeConstraint           = qualifiedVersion TypeConstraint
methodDeclaration        = qualifiedVersion MethodDeclaration
methodImplementation     = qualifiedVersion MethodImplementation
constructorDeclaration a = qualifiedVersion ConstructorDeclaration a

----

simpleTestCases :: [(Expr, ExprL)]
simpleTestCases = [
    (lamE "x" (varE "x"),
     LamL 0 (VarL 0)),

    (lamE "x" (lamE "x" (varE "x")),
     LamL 0 (LamL 1 (VarL 1))),

    (lamE "x" (lamE "y" (varE "x")),
     LamL 0 (LamL 1 (VarL 0))),

    (lamE "x" (lamE "y" (varE "y")),
     LamL 0 (LamL 1 (VarL 1))),

    (lamE "x" (lamE "y" (naAppE (varE "x") (varE "y"))),
     LamL 0 (LamL 1 (AppL (VarL 0) (VarL 1)))),

    (lamE "x" (naAppE
                (lamE "y" (lamE "x" (naAppE (varE "x") (varE "y"))))
                (varE "x")),
     LamL 0 (AppL
                (LamL 1 (LamL 2 (AppL (VarL 2) (VarL 1))))
                (VarL 0))),

    (lamE "x" $ lamE "y" $ lamE "z" $
        naTupleE [varE "z", varE "y", varE "x"],
     LamL 0 $ LamL 1 $ LamL 2 $
        RecordL [VarL 2, VarL 1, VarL 0]),

    (naLetE [
           valueD "x" Nothing (naConstantE (FixnumC 1))
       ] (varE "x"),
     LetL [
           ValueDL 0 (ConstantL (FixnumC 1))
       ] (VarL 0)),

    (naLetE [
           valueD "x" Nothing (varE "y"),
           valueD "y" Nothing (varE "z"),
           valueD "z" Nothing (varE "x")
       ] (varE "x"),
     LetL [
           ValueDL 0 (VarL 1),
           ValueDL 1 (VarL 2),
           ValueDL 2 (VarL 0)
       ] (VarL 0)),

    ---- Test functionality for collecting lambdas

    (naLetE [
           valueD "f" Nothing (lamE "x" (lamE "y" (lamE "z" (varE "x"))))
       ] (varE "f"),
     LetL [
           ValueDL 0 (LamL 1 $ LamL 2 $ LamL 3 $ VarL 1)
       ] (VarL 0)),

    ---- Test constructor representation

    -- One constructor with no arguments
    -- Represent it as the constant 0
    (naLetE [
         datatypeD "T" []
           [
             constructorDeclaration "A"
               []
           ]
       ] (constructorE "A"),
     ConstantL (FixnumC 0)),

    -- One constructor with one argument
    -- Represent it as the argument itself
    (naLetE [
         datatypeD "T" []
           [
             constructorDeclaration "A"
               [primTFixnum]
           ]
       ] (constructorE "A"),
     LamL 0 $ VarL 0),

    -- One constructor with many arguments
    -- Represent it as a record but with no tag
    (naLetE [
         datatypeD "T" []
           [
             constructorDeclaration "A"
               [primTFixnum, primTFixnum, primTFixnum]
           ]
       ] (constructorE "A"),
     LamL 0 $ LamL 1 $ LamL 2 $ RecordL [VarL 0, VarL 1, VarL 2]),

    -- Many constructors
    -- - No arguments:   represent them as constants
    -- - With arguments: represent them as records with a tag.
    --                   If every other constructor is constant,
    --                   drop the tag.

    (naLetE [
         datatypeD "T" []
           [
             constructorDeclaration "B"
               [primTFixnum],
             constructorDeclaration "D"
               [primTFixnum, primTFixnum, primTFixnum],
             constructorDeclaration "C"
               [primTFixnum, primTFixnum],
             constructorDeclaration "A"
               []
           ]
       ] (constructorE "A"),
     ConstantL (FixnumC 3)),

    (naLetE [
         datatypeD "T" []
           [
             constructorDeclaration "B"
               [primTFixnum],
             constructorDeclaration "D"
               [primTFixnum, primTFixnum, primTFixnum],
             constructorDeclaration "C"
               [primTFixnum, primTFixnum],
             constructorDeclaration "A"
               []
           ]
       ] (constructorE "B"),
     LamL 0 $ RecordL [ConstantL (FixnumC 0), VarL 0]),

    (naLetE [
         datatypeD "T" []
           [
             constructorDeclaration "B"
               [primTFixnum],
             constructorDeclaration "D"
               [primTFixnum, primTFixnum, primTFixnum],
             constructorDeclaration "C"
               [primTFixnum, primTFixnum],
             constructorDeclaration "A"
               []
           ]
       ] (constructorE "C"),
     LamL 0 $ LamL 1 $
     RecordL [ConstantL (FixnumC 2), VarL 0, VarL 1]),

    (naLetE [
         datatypeD "T" []
           [
             constructorDeclaration "B"
               [primTFixnum],
             constructorDeclaration "D"
               [primTFixnum, primTFixnum, primTFixnum],
             constructorDeclaration "C"
               [primTFixnum, primTFixnum],
             constructorDeclaration "A"
               []
           ]
       ] (constructorE "D"),
     LamL 0 $ LamL 1 $ LamL 2 $
     RecordL [ConstantL (FixnumC 1), VarL 0, VarL 1, VarL 2]),

    -- Safe untagged constructor
    (naLetE [
         datatypeD "T" []
           [
             constructorDeclaration "A"
               [],
             constructorDeclaration "B"
               [],
             constructorDeclaration "C"
               [primTFixnum, primTFixnum, primTFixnum],
             constructorDeclaration "D"
               []
           ]
       ] (constructorE "C"),
     LamL 0 $ LamL 1 $ LamL 2 $
     RecordL [VarL 0, VarL 1, VarL 2]),

    (naConstructorE (QualifId primPackage primReferenceNew),
     LamL 0 $ PrimitiveL PrimRef [VarL 0]),

    (naVarE (QualifId primPackage primReferenceDeref),
     LamL 0 $ PrimitiveL PrimDeref [VarL 0]),

    ---- Test matching compiler

    -- Empty branches
    (naMatchE (naTupleE [])
       [
         MatchBranch (naTupleP []) (naConstantE (FixnumC 1))
       ],
     AppL (LamL 0 (ConstantL (FixnumC 1))) (RecordL [])),

    -- Tuple structures
    (naMatchE (naTupleE [naTupleE [], naTupleE []])
       [
         MatchBranch (naTupleP [naTupleP [], naTupleP []])
                     (naConstantE (FixnumC 1))
       ],
     AppL
       (LamL 0
         (AppL
           (AppL
             (LamL 1 $ LamL 2 $
               (ConstantL (FixnumC 1)))
             (SelectL 0 (VarL 0)))
           (SelectL 1 (VarL 0))))
       (RecordL [RecordL [], RecordL []])),

    -- Variables
    (naMatchE (naConstantE (FixnumC 1))
       [
         MatchBranch (varP "x")
                     (varE "x")
       ],
     AppL
       (LamL 0 (VarL 0))
       (ConstantL (FixnumC 1))
    ),

    -- Tuples with variables (and wildcards)
    (naMatchE (naTupleE [
                 naConstantE (FixnumC 1),
                 naConstantE (FixnumC 2)
               ])
       [ MatchBranch (naTupleP [varP "x", varP "y"]) (varE "x") ],
     AppL
       (LamL 0
           (foldl AppL
                  (LamL 1 $ LamL 2 $ VarL 1)
                  [SelectL 0 (VarL 0), SelectL 1 (VarL 0)]))
       (RecordL [ConstantL (FixnumC 1), ConstantL (FixnumC 2)])
    ),

    (naMatchE (naTupleE [
                 naConstantE (FixnumC 1),
                 naConstantE (FixnumC 2)
               ])
       [ MatchBranch (naTupleP [varP "x", varP "y"]) (varE "y") ],
     AppL
       (LamL 0
           (foldl AppL
                  (LamL 1 $ LamL 2 $ VarL 2)
                  [SelectL 0 (VarL 0), SelectL 1 (VarL 0)]))
       (RecordL [ConstantL (FixnumC 1), ConstantL (FixnumC 2)])
    ),

    (naMatchE (naTupleE [
                 naConstantE (FixnumC 1),
                 naConstantE (FixnumC 2)
               ])
       [ MatchBranch (naTupleP [naAnyP, varP "y"]) (varE "y") ],
     AppL
       (LamL 0
           (foldl AppL
                  (LamL 1 $ LamL 2 $ VarL 2)
                  [SelectL 0 (VarL 0), SelectL 1 (VarL 0)]))
       (RecordL [ConstantL (FixnumC 1), ConstantL (FixnumC 2)])
    ),

    (naMatchE (naTupleE [
                 naConstantE (FixnumC 1),
                 naConstantE (FixnumC 2)
               ])
       [ MatchBranch (naTupleP [naAnyP, naAnyP]) (naConstantE (FixnumC 1)) ],
     AppL
       (LamL 0
           (foldl AppL
                  (LamL 1 $ LamL 2 $ ConstantL (FixnumC 1))
                  [SelectL 0 (VarL 0), SelectL 1 (VarL 0)]))
       (RecordL [ConstantL (FixnumC 1), ConstantL (FixnumC 2)])
    ),

    -- Constants

    (naMatchE (naConstantE (FixnumC 1))
       [
         MatchBranch (naConstantP (FixnumC 2))
                     (naConstantE (FixnumC 20)),
         MatchBranch (naConstantP (FixnumC 1))
                     (naConstantE (FixnumC 10)),
         MatchBranch naAnyP (naConstantE (FixnumC 30))
       ],
     AppL
       (LamL 0
          (LetL
            [
              ValueDL 1
                (LamL 2 (ConstantL (FixnumC 30)))
            ]
            (MatchL MatchLSpansConstants
               (VarL 0)
               [
                  MatchBranchL
                    (ConstantConstructor (FixnumC 1))
                    (ConstantL (FixnumC 10)),
                  MatchBranchL
                    (ConstantConstructor (FixnumC 2))
                    (ConstantL (FixnumC 20))
               ]
               (Just (AppL (VarL 1) (ConstantL (FixnumC 0)))))))
       (ConstantL (FixnumC 1))
    ),

    (naMatchE (naTupleE [
                naConstantE (FixnumC 100),
                naConstantE (FixnumC 101)
               ])
       [
         MatchBranch
           (naTupleP [naConstantP (FixnumC 0), naConstantP (FixnumC 0)])
           (naConstantE (FixnumC 0)),
         MatchBranch
           (naTupleP [naConstantP (FixnumC 0), naConstantP (FixnumC 1)])
           (naConstantE (FixnumC 1)),
         MatchBranch
           (naTupleP [naConstantP (FixnumC 1), naConstantP (FixnumC 0)])
           (naConstantE (FixnumC 1)),
         MatchBranch
           (naTupleP [naConstantP (FixnumC 1), naConstantP (FixnumC 1)])
           (naConstantE (FixnumC 0)),
         MatchBranch naAnyP (naConstantE (FixnumC 30))
       ],
     AppL
       (LamL 0 $
          LetL [
            ValueDL 1
              (LamL 2 $ ConstantL (FixnumC 30))
          ]
          (foldl AppL
              (LamL 3 $ LamL 4 $
                  MatchL MatchLSpansConstants (VarL 3) [
                    MatchBranchL
                      (ConstantConstructor (FixnumC 0))
                      (
                        MatchL MatchLSpansConstants (VarL 4) [
                          MatchBranchL
                            (ConstantConstructor (FixnumC 0))
                            (ConstantL (FixnumC 0)),
                          MatchBranchL
                            (ConstantConstructor (FixnumC 1))
                            (ConstantL (FixnumC 1))
                        ]
                        (Just (AppL (VarL 1) (ConstantL (FixnumC 0))))
                      ),
                    MatchBranchL
                      (ConstantConstructor (FixnumC 1))
                      (
                        MatchL MatchLSpansConstants (VarL 4) [
                          MatchBranchL
                            (ConstantConstructor (FixnumC 0))
                            (ConstantL (FixnumC 1)),
                          MatchBranchL
                            (ConstantConstructor (FixnumC 1))
                            (ConstantL (FixnumC 0))
                        ]
                        (Just (AppL (VarL 1) (ConstantL (FixnumC 0))))
                      )
                  ]
                  (Just (AppL (VarL 1) (ConstantL (FixnumC 0))))
              )
              [SelectL 0 (VarL 0), SelectL 1 (VarL 0)])
       )
       (RecordL [ConstantL (FixnumC 100), ConstantL (FixnumC 101)])
    ),

    (naMatchE (naTupleE [
                naConstantE (FixnumC 100),
                naConstantE (FixnumC 101)
               ])
       [
         MatchBranch
           (naTupleP [naConstantP (FixnumC 0), varP "x"])
           (varE "x"),
         MatchBranch
           (naTupleP [varP "x", naConstantP (FixnumC 1)])
           (varE "x"),
         MatchBranch naAnyP (naConstantE (FixnumC 30))
       ],
     AppL
       (LamL 0 $
          LetL [
            ValueDL 1
              (LamL 2 $ ConstantL (FixnumC 30))
          ]
          (foldl AppL
              (LamL 3 $ LamL 4 $
                  LetL [
                    ValueDL 5
                    (LamL 6 $ MatchL MatchLSpansConstants (VarL 4) [
                       MatchBranchL
                         (ConstantConstructor (FixnumC 1))
                         (VarL 3)
                     ] (Just (AppL (VarL 1) (ConstantL (FixnumC 0)))))
                  ]
                  (MatchL MatchLSpansConstants (VarL 3) [
                     MatchBranchL
                       (ConstantConstructor (FixnumC 0))
                       (VarL 4)
                   ]
                   (Just (AppL (VarL 5) (ConstantL $ FixnumC 0))))
              )
              [SelectL 0 (VarL 0), SelectL 1 (VarL 0)]))
       (RecordL [ConstantL (FixnumC 100), ConstantL (FixnumC 101)])
    ),

    ---- Constructors

    -- Tagged
    (naLetE [
         datatypeD "T" []
           [
             constructorDeclaration "A" [primTFixnum],
             constructorDeclaration "B" [primTFixnum]
           ]
     ] (naMatchE (naAppE (constructorE "A")
                         (naConstantE (FixnumC 10))) [
         MatchBranch (constructorP "A" [varP "x"])
                     (varE "x"),
         MatchBranch (constructorP "B" [varP "x"])
                     (varE "x")
     ])
    ,
     AppL
       (LamL 0 $
          MatchL (MatchLSpansConstructors [
                   TaggedCR 0,
                   TaggedCR 1
                 ])
                 (VarL 0) [
            MatchBranchL
              (DataConstructor (TaggedCR 0))
              (AppL
                (LamL 2 (VarL 2))
                (SelectL 1 (VarL 0))),
            MatchBranchL
              (DataConstructor (TaggedCR 1))
              (AppL
                (LamL 3 (VarL 3))
                (SelectL 1 (VarL 0)))
          ] Nothing
       )
       (AppL
         (LamL 1 $
           RecordL [
             ConstantL (FixnumC 0),
             VarL 1
           ])
         (ConstantL (FixnumC 10)))
    ),

    -- A safe untagged, B, C constant
    (naLetE [
         datatypeD "T" []
           [
             constructorDeclaration "A" [constructorT "T" [],
                                         constructorT "T" []],
             constructorDeclaration "B" [],
             constructorDeclaration "C" []
           ]
     ] (naMatchE (naAppE
                   (naAppE (constructorE "A")
                           (constructorE "B"))
                   (constructorE "C")) [
         MatchBranch (constructorP "A" [constructorP "B" [], varP "y"])
                     (naConstantE (FixnumC 101)),
         MatchBranch (constructorP "A" [varP "x", varP "y"])
                     (varE "x"),
         MatchBranch naAnyP
                     (naConstantE (FixnumC 100))
     ])
    ,
     AppL
       (LamL 0 $
          LetL [
            ValueDL 3 (LamL 4 $ ConstantL (FixnumC 100))
          ]
          (MatchL (MatchLSpansConstructors [
                      SafeUntaggedCR,
                      ConstantCR 0,
                      ConstantCR 1
                  ]) (VarL 0) [
            MatchBranchL
              (DataConstructor SafeUntaggedCR)
              (AppL
                (AppL
                  (LamL 5 $ LamL 6 $
                    LetL [
                      ValueDL 7 (LamL 8 $ VarL 5)
                    ]
                    (MatchL (MatchLSpansConstructors [
                        SafeUntaggedCR,
                        ConstantCR 0,
                        ConstantCR 1
                    ]) (VarL 5) [
                      MatchBranchL
                        (DataConstructor (ConstantCR 0))
                        (ConstantL $ FixnumC 101)
                    ] (Just (AppL (VarL 7) (ConstantL $ FixnumC 0))))
                  )
                  (SelectL 0 (VarL 0)))
                (SelectL 1 (VarL 0)))
          ] (Just (AppL (VarL 3) (ConstantL $ FixnumC 0))))
       )
       (AppL
         (AppL
           (LamL 1 $ LamL 2 $
             RecordL [
               VarL 1,
               VarL 2
             ])
           (ConstantL (FixnumC 0)))
         (ConstantL (FixnumC 1)))
    ),

    -- A tagged, B, C constant, D tagged
    (naLetE [
         datatypeD "T" []
           [
             constructorDeclaration "A" [constructorT "T" [],
                                         constructorT "T" []],
             constructorDeclaration "B" [],
             constructorDeclaration "C" [],
             constructorDeclaration "D" [constructorT "T" []]
           ]
     ] (naMatchE (naAppE
                   (naAppE (constructorE "A")
                           (constructorE "B"))
                   (constructorE "C")) [
         MatchBranch (constructorP "A" [constructorP "B" [], varP "y"])
                     (naConstantE (FixnumC 101)),
         MatchBranch (constructorP "A" [varP "x", varP "y"])
                     (varE "x"),
         MatchBranch naAnyP
                     (naConstantE (FixnumC 100))
     ])
    ,
     AppL
       (LamL 0 $
          LetL [
            ValueDL 3 (LamL 4 $ ConstantL (FixnumC 100))
          ]
          (MatchL (MatchLSpansConstructors [
                      TaggedCR 0,
                      ConstantCR 1,
                      ConstantCR 2,
                      TaggedCR 3
                  ]) (VarL 0) [
            MatchBranchL
              (DataConstructor (TaggedCR 0))
              (AppL
                (AppL
                  (LamL 5 $ LamL 6 $
                    LetL [
                      ValueDL 7 (LamL 8 $ VarL 5)
                    ]
                    (MatchL (MatchLSpansConstructors [
                              TaggedCR 0,
                              ConstantCR 1,
                              ConstantCR 2,
                              TaggedCR 3
                            ]) (VarL 5) [
                      MatchBranchL
                        (DataConstructor (ConstantCR 1))
                        (ConstantL $ FixnumC 101)
                    ] (Just (AppL (VarL 7) (ConstantL $ FixnumC 0))))
                  )
                  (SelectL 1 (VarL 0)))
                (SelectL 2 (VarL 0)))
          ] (Just (AppL (VarL 3) (ConstantL $ FixnumC 0))))
       )
       (AppL
         (AppL
           (LamL 1 $ LamL 2 $
             RecordL [
               ConstantL (FixnumC 0),
               VarL 1,
               VarL 2
             ])
           (ConstantL (FixnumC 1)))
         (ConstantL (FixnumC 2)))
    ),

    -- Foreign declarations
    (naLetE [
       naForeignD ForeignLangC "putchar"
                    (QualifId globalPackage "f")
                    (primTFunction primTChar (primTTuple []))
     ] (varE "f"),
     LetL [
       ValueDL 0
               (LamL 1 $ ForeignL
                 (ForeignSignature
                   ForeignLangC "putchar"
                   [ForeignChar] ForeignUnit)
                 [VarL 1])
     ] (VarL 0)
    ),

    -- sentinel
    (naConstantE (FixnumC 1),
     ConstantL (FixnumC 1))
  ]

testN :: Int -> TestResult
testN 1 = rec 0 simpleTestCases
  where
    rec _ [] = testOK
    rec i ((expression, expected):ts)
      | obtained == expected = rec (i + 1) ts
      | otherwise =
        testError ("\nFallo el test " ++
                   "(TestPrecompiler.simpleTestCases !! " ++ show i ++ ")" ++
                   "\nAl precompilar: " ++ show expression ++
                   "\nEsperado: " ++ show expected ++
                   "\nObtenido: " ++ show obtained)
      where obtained :: ExprL
            obtained =
              case precompile expression of
                Left msg -> error ("No se puede precompilar\n" ++ msg)
                Right x  -> x

test :: TestResult
test = mapM_ testN [1]

