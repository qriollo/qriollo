
module Test.TestParser(test) where

import Test.Testing(TestResult, testOK, testError, testMany)

import ExpressionE
import Primitive(primPackage, primMain)
import Primitive(
        primTFunction, primTTuple, primListNil, primListCons, primMain,
        primTPtr, primString, primBoolTrue, primBoolFalse,
        primMonadBind,
    )
import Lexer(Token)
import Parser(
        ParserOptions(..), parseFromStringOrFail,
        parsePackages, parsePackagesOrFail
    )
import Reader(readFromStrings, readFromStringsOrFail)

globalPackage :: PackageName
globalPackage = ["Input"]

globalParserOptions :: ParserOptions
globalParserOptions = ParserOptions {
                        parserOptionsFeatures = []
                      }

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

qualifiedMatchingLamE :: (Id -> QualifId) -> [Id] -> [Int] -> Expr -> Expr
qualifiedMatchingLamE qualifier ids freshNs body =
        foldr naLamE (naMatchE (naTupleE (map naVarE qFreshIds))
                               [MatchBranch (naTupleP (map naVarP qIds)) body])
                   qFreshIds
  where
    qFreshIds = map (\ n -> QualifId primPackage ("{parser|" ++ show n ++ "}"))
                    freshNs
    qIds = map qualifier ids

matchingLamE :: [Id] -> [Int] -> Expr -> Expr
matchingLamE = qualifiedMatchingLamE qualifyGlobally

simpleTestCases :: [(String, Declaration)]
simpleTestCases = [
    ("el fulano es x", valueD "fulano" Nothing $
      varE "x"),

    ("el fulano es y", valueD "fulano" Nothing $
      varE "y"),

    ("el fulano es x y", valueD "fulano" Nothing $
      naAppE (varE "x") (varE "y")),

    ("el fulano es x y z", valueD "fulano" Nothing $
      naAppE (naAppE (varE "x") (varE "y")) (varE "z")),

    ("el fulano es x (y z)", valueD "fulano" Nothing $
      naAppE (varE "x") (naAppE (varE "y") (varE "z"))),

    ("el fulano es x z (y z)", valueD "fulano" Nothing $
      naAppE (naAppE (varE "x") (varE "z")) (naAppE (varE "y") (varE "z"))),

    ("el fulano es (x z) (y z)", valueD "fulano" Nothing $
      naAppE (naAppE (varE "x") (varE "z")) (naAppE (varE "y") (varE "z"))),

    ("el fulano es ante x da x", valueD "fulano" Nothing $
      lamE "x" (varE "x")),

    ("el fulano es el que dado x da x", valueD "fulano" Nothing $
      matchingLamE ["x"] [0] (varE "x")),

    ("el fulano es la que dada x da x", valueD "fulano" Nothing $
      matchingLamE ["x"] [0] (varE "x")),

    ("el fulano es ante x y z da x", valueD "fulano" Nothing $
      lamE "x" (lamE "y" (lamE "z" (varE "x")))),

    ("el fulano es el que dados x y z da x", valueD "fulano" Nothing $
      matchingLamE ["x", "y", "z"] [0..2] (varE "x")),

    ("el fulano es la que dadas x y z da x", valueD "fulano" Nothing $
      matchingLamE ["x", "y", "z"] [0..2] (varE "x")),

    ("el fulano es la que dadas x y z da x y", valueD "fulano" Nothing $
      matchingLamE ["x", "y", "z"] [0..2] (naAppE (varE "x") (varE "y"))),

    ("el fulano es (la que dadas x y z da x) y", valueD "fulano" Nothing $
      naAppE (matchingLamE ["x", "y", "z"] [0..2] (varE "x")) (varE "y")),

    ("el fulano es ()",
     valueD "fulano" Nothing $ naTupleE []),
    ("el fulano es (x)",
     valueD "fulano" Nothing $ varE "x"),
    ("el fulano es (x,y)",
     valueD "fulano" Nothing $ naTupleE [varE "x", varE "y"]),
    ("el fulano es (x,y,)",
     valueD "fulano" Nothing $ naTupleE [varE "x", varE "y"]),
    ("el fulano es (x,y,z)",
     valueD "fulano" Nothing $ naTupleE [varE "x", varE "y", varE "z"]),
    ("el fulano es (x,y,z,)",
     valueD "fulano" Nothing $ naTupleE [varE "x", varE "y", varE "z"]),

    -- Test left and right associativity

    ("chirimbolo zurdo 10 + \n el fulano es x + y + z",
      valueD "fulano" Nothing $
      app2 (varE "+")
           (app2 (varE "+") (varE "x") (varE "y"))
           (varE "z")),

    ("chirimbolo diestro 10 + \n el fulano es x + y + z",
      valueD "fulano" Nothing $
      app2 (varE "+")
           (varE "x")
           (app2 (varE "+") (varE "y") (varE "z"))),

    -- Test prefix operators
    ("chirimbolo prefijo 10 ! \n el fulano es ! ! !x",
      valueD "fulano" Nothing $
      naAppE (varE "!")
           (naAppE (varE "!")
                 (naAppE (varE "!")
                       (varE "x")))),

    -- Test constructor operators

    ("chirimbolo diestro 10 :: \n el fulano es x :: y :: z :: Nil",
     valueD "fulano" Nothing $
     app2 (constructorE "::") (varE "x")
          (app2 (constructorE "::") (varE "y")
          (app2 (constructorE "::") (varE "z") (constructorE "Nil")))),

    -- Test precedence

    ("chirimbolo zurdo 10 + chirimbolo zurdo 10 - \n el fulano es x - y + z",
     valueD "fulano" Nothing $
     app2 (varE "+")
          (app2 (varE "-") (varE "x") (varE "y"))
          (varE "z")),

    ("chirimbolo zurdo 10 + chirimbolo zurdo 10 - \n el fulano es x + y - z",
     valueD "fulano" Nothing $
     app2 (varE "-")
          (app2 (varE "+") (varE "x") (varE "y"))
          (varE "z")),

    ("chirimbolo zurdo 5 + chirimbolo zurdo 10 * \n el fulano es x * y + z",
     valueD "fulano" Nothing $
     app2 (varE "+")
          (app2 (varE "*") (varE "x") (varE "y"))
          (varE "z")),

    ("chirimbolo zurdo 5 + chirimbolo zurdo 10 * \n el fulano es x + y * z",
     valueD "fulano" Nothing $
     app2 (varE "+")
          (varE "x")
          (app2 (varE "*") (varE "y") (varE "z"))),

    ("chirimbolo zurdo 5 + chirimbolo zurdo 10 * \n el fulano es (x + y) * z",
     valueD "fulano" Nothing $
     app2 (varE "*")
          (app2 (varE "+") (varE "x") (varE "y"))
          (varE "z")),

    ("chirimbolo zurdo 10 ** " ++
     "chirimbolo prefijo 20 ?? \n" ++
     " el fulano es ?? a ** ?? b",
     valueD "fulano" Nothing $
     app2 (varE "**") (naAppE (varE "??") (varE "a"))
                      (naAppE (varE "??") (varE "b"))),

    ("chirimbolo zurdo 30 ** " ++
     "chirimbolo prefijo 20 ?? \n" ++
     " el fulano es ?? a ** b",
     valueD "fulano" Nothing $
     naAppE (varE "??") (app2 (varE "**") (varE "a") (varE "b"))),

    -- Lists
    ("el programa es []",
     valueD "programa" Nothing nil),

    ("el programa es [10#]",
     valueD "programa" Nothing
       (cons
         (naConstantE (FixnumC 10))
         nil)),

    ("el programa es [10#,]",
     valueD "programa" Nothing
       (cons
         (naConstantE (FixnumC 10))
         nil)),

    ("el programa es [1#,2#,3#]",
     valueD "programa"
        Nothing
        (cons
          (naConstantE (FixnumC 1))
          (cons
            (naConstantE (FixnumC 2))
            (cons
              (naConstantE (FixnumC 3))
              nil)))),

    -- Monadic let
    ("el programa es " ++
     " che la x es 1# " ++
     " che la y es 2# " ++
     " en " ++
     "   (x, y) "
     ,
     valueD "programa"
        Nothing
        (app2 (naVarE (QualifId primPackage primMonadBind))
              (naConstantE (FixnumC 1))
              (lamE "x"
                (app2 (naVarE (QualifId primPackage primMonadBind))
                  (naConstantE (FixnumC 2))
                  (lamE "y"
                    (naTupleE [
                      varE "x",
                      varE "y"
                    ])))))),

    ("el programa es " ++
     " che la x de Numerito es 1# " ++
     " che la y es 2# " ++
     " en " ++
     "   (x, y) "
     ,
     valueD "programa"
        Nothing
        (app2 (naVarE (QualifId primPackage primMonadBind))
              (naLetE
                 [naValueD (QualifId primPackage "{parser|0}")
                           (Just
                             (ConstrainedType []
                               (naConstructorT
                                 (QualifId primPackage
                                          "Numerito"))))
                           (naConstantE (FixnumC 1))]
                 (naVarE (QualifId primPackage "{parser|0}")))
              (lamE "x"
                (app2 (naVarE (QualifId primPackage primMonadBind))
                  (naConstantE (FixnumC 2))
                  (lamE "y"
                    (naTupleE [
                      varE "x",
                      varE "y"
                    ])))))),

    ("el programa es " ++
     " che 1# en x ",
     valueD "programa"
        Nothing
        (app2 (naVarE (QualifId primPackage primMonadBind))
              (naConstantE (FixnumC 1))
              (naLamE (QualifId primPackage "_") 
                (varE "x")))),

    -- If-then-else
    ("el programa es si Sí da 1# si no da 2#",
     valueD "programa" Nothing $
       naMatchE (naConstructorE (QualifId primPackage primBoolTrue)) [
         MatchBranch
           (naConstructorP (QualifId primPackage primBoolTrue) [])
           (naConstantE (FixnumC 1)),
         MatchBranch
           naAnyP
           (naConstantE (FixnumC 2))
       ]
    ),

    ("el programa es si Sí da 1# si No da 2# si no da 3#",
     valueD "programa" Nothing $
       naMatchE (naConstructorE (QualifId primPackage primBoolTrue)) [
         MatchBranch
           (naConstructorP (QualifId primPackage primBoolTrue) [])
           (naConstantE (FixnumC 1)),
         MatchBranch
           naAnyP
           (naMatchE (naConstructorE (QualifId primPackage primBoolFalse)) [
              MatchBranch
                (naConstructorP (QualifId primPackage primBoolTrue) [])
                (naConstantE (FixnumC 2)),
              MatchBranch
                naAnyP
                (naConstantE (FixnumC 3))
           ])
       ]
    ),

    -- If-then-else inside a matching declaration
    ("el programa dado n si f n da 1# si no da 2#",
     valueD "programa" Nothing $
     (matchingLamE ["n"] [0]
       (naMatchE (naAppE (varE "f") (varE "n")) [
         MatchBranch
           (naConstructorP (QualifId primPackage primBoolTrue) [])
           (naConstantE (FixnumC 1)),
         MatchBranch
           naAnyP 
           (naConstantE (FixnumC 2))
       ]))
    ),

    -- Strings
    ("el programa es \"\"",
     valueD "programa" Nothing (mkString nil)),

    ("el programa es \"a\"",
     valueD "programa" Nothing
       (mkString (cons (naConstantE (CharC 'a')) nil))),

    ("el programa es \"abc\"",
     valueD "programa" Nothing
            (mkString
              (cons
                 (naConstantE (CharC 'a'))
                 (cons
                   (naConstantE (CharC 'b'))
                   (cons
                     (naConstantE (CharC 'c'))
                     nil))))),

    -- Test basic types
    ("el fulano de Ent es x",
     valueD "fulano"
        (Just
            (ConstrainedType [] (constructorT "Ent" [])))
        (varE "x")),

    ("el fulano de Ent de Ent es x",
     valueD "fulano"
        (Just
            (ConstrainedType []
                (constructorT "Ent" [constructorT "Ent" []])))
        (varE "x")),

    ("el fulano de Lista_ de (Lista_ de Ent) es x",
     valueD "fulano"
        (Just (ConstrainedType []
                (constructorT "Lista_" [
                  constructorT "Lista_" [
                    constructorT "Ent" []]])))
        (varE "x")),

    ("el fulano de Lista_ de (Lista_ de a) es x",
     valueD "fulano"
            (Just (ConstrainedType []
                   (constructorT "Lista_" [
                    constructorT "Lista_" [varT "a" []]])))
            (varE "x")),

    ("el map de (coso en cosito) en Lista_ de coso en Lista_ de cosito es x",
     valueD "map"
            (Just (ConstrainedType []
                    (primTFunction
                      (primTFunction (varT "coso" []) (varT "cosito" []))
                      (primTFunction
                        (constructorT "Lista_" [varT "coso" []])
                        (constructorT "Lista_" [varT "cosito" []])))))
            (varE "x")),

    -- Datatype declarations
    ("un A es bien A",
     datatypeD "A" [] [constructorDeclaration "A" []]),
    ("un Par de coso cosito es bien Par coso cosito",
     datatypeD "Par" ["coso", "cosito"] [
        constructorDeclaration "Par" [varT "coso" [], varT "cosito" []]]),
    ("un Par de coso cosito es bien Par (coso, cosito)",
     datatypeD "Par" ["coso", "cosito"] [
        constructorDeclaration "Par" [
            primTTuple [varT "coso" [], varT "cosito" []]]]),
    ("una Lista_ de coso es bien Vacía_ bien Agregar coso (Lista_ de coso)",
     datatypeD "Lista_" ["coso"] [
        constructorDeclaration "Vacía_" [],
        constructorDeclaration "Agregar" [
            varT "coso" [],
            constructorT "Lista_" [varT "coso" []]]]),

    -- Type alias declarations
    ("un A es A",
     typeD "A" [] (constructorT "A" [])),
    ("una Función_ de a b es a en b",
     typeD "Función_" ["a", "b"] (primTFunction (varT "a" []) (varT "b" []))),

    -- Pattern matching
    ("el resultado es mirar x si x da x si y da y boludo",
     valueD "resultado" Nothing
                        (naMatchE (varE "x") [
                          MatchBranch (varP "x") (varE "x"),
                          MatchBranch (varP "y") (varE "y")
                        ])),

    ("el resultado es mirar x si (y, z) da y boludo",
     valueD "resultado"
            Nothing
            (naMatchE (varE "x") [
              MatchBranch (naTupleP [varP "y", varP "z"]) (varE "y")
            ])),

    ("el resultado es mirar x si x da x si no da y boludo",
     valueD "resultado"
            Nothing
            (naMatchE (varE "x") [
              MatchBranch (varP "x") (varE "x"),
              MatchBranch naAnyP (varE "y")
            ])),
    ("el resultado es mirar x si _ da x boludo",
     valueD "resultado"
            Nothing
            (naMatchE (varE "x") [ MatchBranch naAnyP (varE "x") ])),
    ("el resultado es mirar lista si Cons x xs da x boludo",
     valueD "resultado"
            Nothing
            (naMatchE (varE "lista") [
                MatchBranch (constructorP "Cons" [varP "x", varP "xs"])
                            (varE "x")
            ])),
    ("el resultado es mirar lista si Cons x Nil da x boludo",
     valueD "resultado"
            Nothing
            (naMatchE (varE "lista") [
                MatchBranch
                    (constructorP "Cons" [varP "x", constructorP "Nil" []])
                    (varE "x")
            ])),
    ("chirimbolo diestro 10 :: " ++
     " el resultado es mirar lista si x :: Nil da x boludo",
     valueD "resultado"
            Nothing
            (naMatchE (varE "lista") [
              MatchBranch
                (constructorP "::" [varP "x", constructorP "Nil" []])
                (varE "x")])),

    -- Operator slices
    ("el por es el *",
     valueD "por" Nothing (varE "*")),
    ("el por es junar (el *)",
     valueD "por" Nothing (naAppE (varE "junar") (varE "*"))),

    ("el resultado es ponele que el x es 1# en x",
      valueD "resultado"
             Nothing
             (naLetE [valueD "x" Nothing (naConstantE (FixnumC 1))]
                     (varE "x"))),
    ("el resultado es ponele que " ++
     "   el x es 1# " ++
     "   la f dado x da x " ++
     "en f x", valueD "resultado" Nothing
     (naLetE [
             valueD "x" Nothing (naConstantE (FixnumC 1)),
             valueD "f" Nothing (matchingLamE ["x"] [0] (varE "x"))
           ]
           (naAppE (varE "f") (varE "x")))),

    -- Chained declarations
    ("el factorial dado 0# da 1# dado n da mul n (factorial (sub n 1#))",
     valueD "factorial"
       Nothing
       (naLamE (QualifId primPackage "{parser|0}")
         (naMatchE (naTupleE [naVarE (QualifId primPackage "{parser|0}")]) [
           MatchBranch
             (naTupleP [naConstantP (FixnumC 0)])
             (naConstantE (FixnumC 1)),
           MatchBranch
             (naTupleP [varP "n"])
             (app2 (varE "mul")
                   (varE "n")
                   (naAppE (varE "factorial")
                           (app2 (varE "sub")
                                 (varE "n")
                                 (naConstantE (FixnumC 1)))))
         ]))),

    ("el y dados Sí_ x da x dados No_ _ da No_",
     valueD "y"
       Nothing
       (naLamE (QualifId primPackage "{parser|0}")
               (naLamE (QualifId primPackage "{parser|1}")
                 (naMatchE
                   (naTupleE [
                      naVarE (QualifId primPackage "{parser|0}"),
                      naVarE (QualifId primPackage "{parser|1}")])
                   [ MatchBranch
                       (naTupleP [constructorP "Sí_" [], varP "x"])
                       (varE "x"),
                     MatchBranch
                       (naTupleP [constructorP "No_" [], naAnyP])
                       (constructorE "No_") ])))),

    ("la f " ++
     "  dado 1# da x  donde la x es 0# boludo " ++
     "  dado 2# da x  donde la x es 1# boludo ",
     valueD "f"
       Nothing
       (naLamE (QualifId primPackage "{parser|0}")
         (naMatchE
           (naTupleE [
              naVarE (QualifId primPackage "{parser|0}") ])
           [ MatchBranch
               (naTupleP [naConstantP (FixnumC 1)])
               (naLetE [valueD "x" Nothing (naConstantE (FixnumC 0))]
                       (varE "x")),
             MatchBranch
               (naTupleP [naConstantP (FixnumC 2)])
               (naLetE [valueD "x" Nothing (naConstantE (FixnumC 1))]
                       (varE "x"))]))),

    -- Where
    ("el x es y donde el y es 1# boludo",
     valueD "x"
       Nothing
       (naLetE [ valueD "y" Nothing (naConstantE (FixnumC 1)) ]
               (varE "y"))),
    ("el x es f 1# donde la f dado 1# da 2# boludo",
     valueD "x"
       Nothing
       (naLetE [
         valueD "f"
           Nothing
           (naLamE
             (QualifId primPackage "{parser|0}")
             (naMatchE
               (naTupleE [naVarE (QualifId primPackage "{parser|0}")]) [
                 MatchBranch
                   (naTupleP [naConstantP (FixnumC 1)])
                   (naConstantE (FixnumC 2)) ]))]
         (naAppE (varE "f") (naConstantE (FixnumC 1))))),

    -- Constraints for types
    ("el x de a en b con Ord para a es 1#",
     valueD "x"
       (Just
        (ConstrainedType
          [typeConstraint "Ord" (varT "a" [])]
          (primTFunction (varT "a" []) (varT "b" []))))
       (naConstantE (FixnumC 1))),

    ("el x de a en b con (Ord para a) es 1#",
     valueD "x"
       (Just
         (ConstrainedType
           [typeConstraint "Ord" (varT "a" [])]
           (primTFunction (varT "a" []) (varT "b" []))))
       (naConstantE (FixnumC 1))),

    ("el x de a en b con (Ord para a,) es 1#",
     valueD "x" 
       (Just
         (ConstrainedType
            [typeConstraint "Ord" (varT "a" [])]
            (primTFunction (varT "a" []) (varT "b" []))))
       (naConstantE (FixnumC 1))),

    ("el x de a en b con (Ord para a, Ord para b) es 1#",
     valueD "x" (Just (ConstrainedType [
                            typeConstraint "Ord" (varT "a" []),
                            typeConstraint "Ord" (varT "b" [])
                       ] (primTFunction (varT "a" []) (varT "b" []))))
                (naConstantE (FixnumC 1))),

    -- Class declarations
    ("cualidad Orden para coso boludo", classD "Orden" "coso" []),
    ("cualidad Orden para fulano " ++
     "   el < de fulano en fulano " ++
     "boludo",
     classD "Orden" "fulano" [
        methodDeclaration "<"
            (ConstrainedType []
                (primTFunction (varT "fulano" []) (varT "fulano" [])))
     ]),
    ("cualidad Mostrar para fulano " ++
     "   el convertir de fulano en Texto_ " ++
     "boludo",
     classD "Mostrar" "fulano" [
        methodDeclaration "convertir"
            (ConstrainedType []
                (primTFunction (varT "fulano" []) (constructorT "Texto_" [])))
     ]),
    ("cualidad Grupo para g " ++
     "   el neutro    de g " ++
     "   la operación de g en g en g " ++
     "boludo",
     classD "Grupo" "g" [
        methodDeclaration "neutro" (ConstrainedType [] (varT "g" [])),
        methodDeclaration
            "operación"
            (ConstrainedType []
                (primTFunction (varT "g" [])
                 (primTFunction (varT "g" [])
                    (varT "g" []))))
     ]),
    ("cualidad Funtor para contenedor " ++
     "   el aplicar de (coso en cosito) " ++
     "              en contenedor de coso " ++
     "              en contenedor de cosito " ++
     "boludo",
     classD "Funtor" "contenedor" [
        methodDeclaration "aplicar"
          (ConstrainedType []
            (primTFunction
                (primTFunction (varT "coso" []) (varT "cosito" []))
                (primTFunction
                  (varT "contenedor" [varT "coso" []])
                  (varT "contenedor" [varT "cosito" []]))))
     ]),
    ("cualidad Mónada_ para caja " ++
     "   el dar    de coso " ++
     "             en caja de coso " ++
     "   el juntar de (coso en caja de cosito) " ++
     "             en caja de coso " ++
     "             en caja de cosito " ++
     "boludo",
     classD "Mónada_" "caja" [
        methodDeclaration "dar"
            (ConstrainedType []
                (primTFunction
                    (varT "coso" [])
                    (varT "caja" [varT "coso" []]))),
        methodDeclaration "juntar"
            (ConstrainedType []
                (primTFunction
                    (primTFunction
                        (varT "coso" [])
                        (varT "caja" [varT "cosito" []]))
                    (primTFunction
                        (varT "caja" [varT "coso" []])
                        (varT "caja" [varT "cosito" []]))))
     ]),
    ("cualidad Buscable para bolsa " ++
     "   el encontrar de coso en bolsa de coso en Nat " ++
     "                con Igualdad para coso " ++
     "boludo",
     classD "Buscable" "bolsa" [
        methodDeclaration "encontrar"
          (ConstrainedType [typeConstraint "Igualdad" (varT "coso" [])]
            (primTFunction (varT "coso" [])
                    (primTFunction
                      (varT "bolsa" [varT "coso" []])
                      (constructorT "Nat" []))))
     ]),

    -- Instances
    ("encarnar Orden para Ent boludo",
     instanceD "Orden"
        (ConstrainedType [] (constructorT "Ent" []))
        []),
    ("encarnar Orden para (a, b) boludo",
     instanceD "Orden"
        (ConstrainedType [] (primTTuple [varT "a" [], varT "b" []]))
        []),
    ("encarnar Orden para Par de a b " ++
     "                con (Orden para a, Orden para b) " ++
     "boludo",
     instanceD "Orden"
        (ConstrainedType
            [typeConstraint "Orden" (varT "a" []),
             typeConstraint "Orden" (varT "b" [])]
            (constructorT "Par" [varT "a" [], varT "b" []])) []),
    (" encarnar Orden para Par de a b " ++
     "                 con (Orden para a, Orden para b) " ++
     "   la x es 1# " ++
     "   la y es 2# " ++
     " boludo ",
        instanceD "Orden"
            (ConstrainedType
                [typeConstraint "Orden" (varT "a" []),
                 typeConstraint "Orden" (varT "b" [])]
                (constructorT "Par" [varT "a" [], varT "b" []]))
            [
              methodImplementation "x" (naConstantE (FixnumC 1)),
              methodImplementation "y" (naConstantE (FixnumC 2))
            ]),

    -- Foreign declarations
    (" gringo C \"fopen\" abrir_archivo de Cadena en Cadena " ++
     "                                            en Pendorcho \"A\" ",
       naForeignD ForeignLangC
                  "fopen"
                  (QualifId globalPackage "abrir_archivo")
                  (primTFunction
                    (constructorT "Cadena" [])
                    (primTFunction
                      (constructorT "Cadena" [])
                      (primTPtr "A")))),

    -- Sentinel
    ("el fulano es 1#",
     valueD "fulano" Nothing (naConstantE (FixnumC 1)))
 ]
 where app2 a b c = naAppE (naAppE a b) c
       cons = app2 $ naConstructorE (QualifId primPackage primListCons)
       nil  = naConstructorE (QualifId primPackage primListNil)
       mkString = naAppE $ naConstructorE (QualifId primPackage primString)

packageTestCases :: [([(PackageName, String)], [Declaration])]
packageTestCases = [
    ([ (["A"], "") ], []),
    ([
       (["A"], "la a es 1#"),
       (["B"], "la b es a")
     ], [
        naValueD (QualifId ["A"] "a") Nothing (naConstantE (FixnumC 1)),
        naValueD (QualifId ["B"] "b") Nothing (naVarE (QualifId ["B"] "a"))
     ]),
    ([
       (["A"], "la a es 1#"),
       (["B"], "enchufar A   la b es a")
     ], [
        naValueD (QualifId ["A"] "a") Nothing (naConstantE (FixnumC 1)),
        naValueD (QualifId ["B"] "b") Nothing (naVarE (QualifId ["A"] "a"))
     ]),
    ([
       (["A"], "la a es 1#"),
       (["B"], "enchufar A(a)   la b es a")
     ], [
        naValueD (QualifId ["A"] "a") Nothing (naConstantE (FixnumC 1)),
        naValueD (QualifId ["B"] "b") Nothing (naVarE (QualifId ["A"] "a"))
     ]),
    ([
       (["A"], "entregar(a)   la a es 1#"),
       (["B"], "enchufar A    la b es a")
     ], [
        naValueD (QualifId ["A"] "a") Nothing (naConstantE (FixnumC 1)),
        naValueD (QualifId ["B"] "b") Nothing (naVarE (QualifId ["A"] "a"))
     ]),
    ([
       (["A"], "entregar(a)   la a es 1#"),
       (["B"], "enchufar A(a) la b es a")
     ], [
        naValueD (QualifId ["A"] "a") Nothing (naConstantE (FixnumC 1)),
        naValueD (QualifId ["B"] "b") Nothing (naVarE (QualifId ["A"] "a"))
     ]),
    ([
       (["A"], "entregar()   la a es 1#"),
       (["B"], "enchufar A   la b es a")
     ], [
        naValueD (QualifId ["A"] "a") Nothing (naConstantE (FixnumC 1)),
        naValueD (QualifId ["B"] "b") Nothing (naVarE (QualifId ["B"] "a"))
     ]),
    ([
       (["A"], "entregar()   la a es 1#"),
       (["B"], "enchufar A() la b es a")
     ], [
        naValueD (QualifId ["A"] "a") Nothing (naConstantE (FixnumC 1)),
        naValueD (QualifId ["B"] "b") Nothing (naVarE (QualifId ["B"] "a"))
     ]),
    ([
       (["A"], "la a es 1#"),
       (["B"], "enchufar A() la b es a")
     ], [
        naValueD (QualifId ["A"] "a") Nothing (naConstantE (FixnumC 1)),
        naValueD (QualifId ["B"] "b") Nothing (naVarE (QualifId ["B"] "a"))
     ]),
    ([
       (["A"], "entregar(a)   la a es 1#"),
       (["B"], "enchufar A(a) la b es a")
     ], [
        naValueD (QualifId ["A"] "a") Nothing (naConstantE (FixnumC 1)),
        naValueD (QualifId ["B"] "b") Nothing (naVarE (QualifId ["A"] "a"))
     ]),
    ([
       (["A"], "la a es 1#"),
       (["B"], ""),
       (["C"], "la c es a")
     ], [
        naValueD (QualifId ["A"] "a") Nothing (naConstantE (FixnumC 1)),
        naValueD (QualifId ["C"] "c") Nothing (naVarE (QualifId ["C"] "a"))
     ]),
    ([
       (["A"], "la a es 1#"),
       (["B"], ""),
       (["C"], "enchufar B   la c es a")
     ], [
        naValueD (QualifId ["A"] "a") Nothing (naConstantE (FixnumC 1)),
        naValueD (QualifId ["C"] "c") Nothing (naVarE (QualifId ["C"] "a"))
     ]),
    ([
       (["A"], "la a es 1#"),
       (["B"], "enchufar A"),
       (["C"], "la c es a")
     ], [
        naValueD (QualifId ["A"] "a") Nothing (naConstantE (FixnumC 1)),
        naValueD (QualifId ["C"] "c") Nothing (naVarE (QualifId ["C"] "a"))
     ]),
    ([
       (["A"], "la a es 1#"),
       (["B"], "enchufar A"),
       (["C"], "enchufar B la c es a")
     ], [
        naValueD (QualifId ["A"] "a") Nothing (naConstantE (FixnumC 1)),
        naValueD (QualifId ["C"] "c") Nothing (naVarE (QualifId ["A"] "a"))
     ]),
    ([
       (["A"], "la a es 1#   la aa es 2#  la aaa es 3#"),
       (["B"], "enchufar A(aa, aaa) la a es 4#"),
       (["C"], "enchufar B(a, aaa) la c es a aa aaa")
     ], [
        naValueD (QualifId ["A"] "a") Nothing (naConstantE (FixnumC 1)),
        naValueD (QualifId ["A"] "aa") Nothing (naConstantE (FixnumC 2)),
        naValueD (QualifId ["A"] "aaa") Nothing (naConstantE (FixnumC 3)),
        naValueD (QualifId ["B"] "a") Nothing (naConstantE (FixnumC 4)),
        naValueD (QualifId ["C"] "c") Nothing
                 (naAppE (naAppE (naVarE (QualifId ["B"] "a"))
                                 (naVarE (QualifId ["C"] "aa")))
                         (naVarE (QualifId ["A"] "aaa")))
     ]),
    ([
       (["A"], "la a es 1#"),
       (["B"], "enchufar A(a como aa)"),
       (["C"], "enchufar B(aa como b) la c es b")
     ], [
        naValueD (QualifId ["A"] "a") Nothing (naConstantE (FixnumC 1)),
        naValueD (QualifId ["C"] "c") Nothing (naVarE (QualifId ["A"] "a"))
     ]),
    ([
       (["A"], "entregar(a, aa, aaa)   la a es 1#   la aa es 2#  la aaa es 3#"),
       (["B"], "enchufar A la b es a aa aaa")
     ], [
        naValueD (QualifId ["A"] "a") Nothing (naConstantE (FixnumC 1)),
        naValueD (QualifId ["A"] "aa") Nothing (naConstantE (FixnumC 2)),
        naValueD (QualifId ["A"] "aaa") Nothing (naConstantE (FixnumC 3)),
        naValueD (QualifId ["B"] "b") Nothing
                 (naAppE (naAppE (naVarE (QualifId ["A"] "a"))
                                 (naVarE (QualifId ["A"] "aa")))
                         (naVarE (QualifId ["A"] "aaa")))
     ]),
    ([
       (["A"], "un ÁrbolBinario de a es " ++
               " bien Vacío " ++
               " bien Bin (ÁrbolBinario de a) a (ÁrbolBinario de a)"),
       (["B"], "enchufar A(Bin, Vacío) " ++
               "el árbol1 de ÁrbolBinario es Bin Vacío x Vacío")
     ], [
        naDatatypeD (QualifId ["A"] "ÁrbolBinario") [(QualifId ["A"] "a")] [
            ConstructorDeclaration (QualifId ["A"] "Vacío") [],
            ConstructorDeclaration (QualifId ["A"] "Bin") [
                naAppT (naConstructorT (QualifId ["A"] "ÁrbolBinario"))
                       (naVarT (QualifId ["A"] "a")),
                naVarT (QualifId ["A"] "a"),
                naAppT (naConstructorT (QualifId ["A"] "ÁrbolBinario"))
                       (naVarT (QualifId ["A"] "a"))
            ]
        ],
        naValueD (QualifId ["B"] "árbol1")
               (Just (ConstrainedType []
                        (naConstructorT (QualifId ["B"] "ÁrbolBinario"))))
               (naAppE
                 (naAppE
                   (naAppE (naConstructorE (QualifId ["A"] "Bin"))
                           (naConstructorE (QualifId ["A"] "Vacío")))
                   (naVarE (QualifId ["B"] "x")))
                 (naConstructorE (QualifId ["A"] "Vacío")))
     ]),
    ([
       (["A"], "chirimbolo diestro 30 :: " ++
               " una Lista_ de coso es " ++
               " bien Nil " ++
               " bien :: coso (Lista_ de coso)"),
       (["B"], "enchufar A(::, Nil) la lista es a :: b :: c :: Nil")
     ], [
        naDatatypeD (QualifId ["A"] "Lista_") [(QualifId ["A"] "coso")] [
            ConstructorDeclaration (QualifId ["A"] "Nil") [],
            ConstructorDeclaration (QualifId ["A"] "::") [
                naVarT (QualifId ["A"] "coso"),
                naAppT (naConstructorT (QualifId ["A"] "Lista_"))
                       (naVarT (QualifId ["A"] "coso"))
            ]],
        naValueD (QualifId ["B"] "lista")
               Nothing
               (app2 (naConstructorE (QualifId ["A"] "::"))
                     (naVarE (QualifId ["B"] "a"))
                     (app2 (naConstructorE (QualifId ["A"] "::"))
                           (naVarE (QualifId ["B"] "b"))
                           (app2 (naConstructorE (QualifId ["A"] "::"))
                                 (naVarE (QualifId ["B"] "c"))
                                 (naConstructorE (QualifId ["A"] "Nil")))))
     ]),
    ([
       (["A"], " chirimbolo zurdo 20 < chirimbolo zurdo 20 > " ++
               " el < es el que dados a b da a " ++
               " el > es el que dados a b da b "),
       (["B"], "enchufar A() el resultado es 1# A.< 2# A.> 3#")
     ], [
        naValueD (QualifId ["A"] "<") Nothing
                                    (qualifiedMatchingLamE
                                      (QualifId ["A"]) ["a", "b"] [0..1]
                                      (naVarE (QualifId ["A"] "a"))),
        naValueD (QualifId ["A"] ">") Nothing
                                    (qualifiedMatchingLamE
                                      (QualifId ["A"]) ["a", "b"] [2..3]
                                      (naVarE (QualifId ["A"] "b"))),
        naValueD (QualifId ["B"] "resultado") Nothing
               (app2 (naVarE (QualifId ["A"] ">"))
                     (app2 (naVarE (QualifId ["A"] "<"))
                           (naConstantE (FixnumC 1))
                           (naConstantE (FixnumC 2)))
                     (naConstantE (FixnumC 3)))
     ]),
    ([
       (["A"], "enchufar B   entregar(a)  la a es B.b"),
       (["B"], "enchufar A   entregar(b)  la b es A.a")
     ], [
        naValueD (QualifId ["A"] "a") Nothing (naVarE (QualifId ["B"] "b")),
        naValueD (QualifId ["B"] "b") Nothing (naVarE (QualifId ["A"] "a"))
     ]),

     ([ (globalPackage,
          " una Persona tiene \n" ++
          "   el nombre de () \n" ++
          "   la edad de PRIM.Numerito \n" ++
          " boludo \n" ++
          " el test1 es \n" ++
          "   Persona cuya edad es 1# \n" ++
          "           cuyo nombre es () \n" ++
          " el test2 es \n" ++
          "   Persona cuyo nombre es () \n" ++
          "           cuya edad es 1# \n" ++
          " el test3 es ante p da \n" ++
          "   p pero cuyo nombre es () \n" ++
          "          cuya edad es 2# \n"
        )
      ], [
        datatypeD "Persona" [] [
          constructorDeclaration "Persona" [
            primTTuple [],
            int
          ]
        ],
        naClassD (QualifId primPackage "{accessor|Input.nombre}")
                 (QualifId primPackage "{record}") [
          MethodDeclaration
            (QualifId ["Input"] "nombre")
            (ConstrainedType [] $
              primTFunction (naVarT (QualifId primPackage "{record}"))
                            (primTTuple [])),
          MethodDeclaration
            (QualifId primPackage "{setter|Input.nombre}")
            (ConstrainedType [] $
              primTFunction
                (naVarT (QualifId primPackage "{record}"))
                (primTFunction
                  (primTTuple [])
                  (naVarT (QualifId primPackage "{record}"))))
        ],
        naClassD (QualifId primPackage "{accessor|Input.edad}")
                 (QualifId primPackage "{record}") [
          MethodDeclaration
            (QualifId ["Input"] "edad")
            (ConstrainedType [] $
              primTFunction (naVarT (QualifId primPackage "{record}"))
                            int),
          MethodDeclaration
            (QualifId primPackage "{setter|Input.edad}")
            (ConstrainedType [] $
              primTFunction
                (naVarT (QualifId primPackage "{record}"))
                (primTFunction
                  int
                  (naVarT (QualifId primPackage "{record}"))))
        ],
        naInstanceD (QualifId primPackage "{accessor|Input.nombre}")
                    (ConstrainedType [] $ constructorT "Persona" []) [
          MethodImplementation
            (QualifId ["Input"] "nombre")
            (naLamE _record
              (naMatchE (naVarE _record) [
                MatchBranch
                  (constructorP "Persona" [
                    (naVarP (_field 0)),
                    (naVarP (_field 1))
                  ])
                  (naVarE (_field 0))
              ])),
          MethodImplementation
            (QualifId primPackage "{setter|Input.nombre}")
            (naLamE _record
              (naLamE _value
                (naMatchE (naVarE _record) [
                  MatchBranch
                    (constructorP "Persona" [
                      (naVarP (_field 0)),
                      (naVarP (_field 1))
                    ])
                    (naAppE
                      (naAppE
                        (constructorE "Persona")
                        (naVarE _value))
                        (naVarE (_field 1)))
                ])))
        ],
        naInstanceD (QualifId primPackage "{accessor|Input.edad}")
                    (ConstrainedType [] $ constructorT "Persona" []) [
          MethodImplementation
            (QualifId ["Input"] "edad")
            (naLamE _record
              (naMatchE (naVarE _record) [
                MatchBranch
                  (constructorP "Persona" [
                    (naVarP (_field 0)),
                    (naVarP (_field 1))
                  ])
                  (naVarE (_field 1))
              ])),
          MethodImplementation
            (QualifId primPackage "{setter|Input.edad}")
            (naLamE _record
              (naLamE _value
                (naMatchE (naVarE _record) [
                  MatchBranch
                    (constructorP "Persona" [
                      (naVarP (_field 0)),
                      (naVarP (_field 1))
                    ])
                    (naAppE
                      (naAppE
                        (constructorE "Persona")
                        (naVarE (_field 0)))
                        (naVarE _value))
                ])))
        ],
        valueD "test1" Nothing
          (naAppE
            (naAppE
              (constructorE "Persona")
              (naTupleE []))
            (naConstantE (FixnumC 1))),
        valueD "test2" Nothing
          (naAppE
            (naAppE
              (constructorE "Persona")
              (naTupleE []))
            (naConstantE (FixnumC 1))),
        valueD "test3" Nothing
          (lamE "p"
            (naAppE
              (naAppE
                (naVarE (QualifId primPackage "{setter|Input.edad}"))
                (naAppE
                  (naAppE
                    (naVarE (QualifId primPackage "{setter|Input.nombre}"))
                    (varE "p"))
                  (naTupleE [])))
              (naConstantE (FixnumC 2))))
      ]),
    -- Sentinel
    ([
       (["A"], "la a es 1#")
     ], [
        naValueD (QualifId ["A"] "a") Nothing (naConstantE (FixnumC 1))
     ])
 ]
 where app2 a b c = naAppE (naAppE a b) c
       _value   = QualifId primPackage "{value}"
       _record  = QualifId primPackage "{record}"
       _field i = QualifId primPackage ("{field|" ++ show i ++ "}")
       int      = naConstructorT $ QualifId primPackage "Numerito"

packageNonTestCases :: [[(PackageName, String)]]
packageNonTestCases = [
    [ (["A"], "a") ],
    [ (["A"], "la a es 1# :: 1#") ],
    [ (["A"], "el fulano es (la que dadas x y z da x ") ],
    [ (["A"], "entregar x") ],
    [ (["A"], "la a es 1#"), (["B"], "enchufar A enchufar A") ],
    [ (["A"], "la a es 1#"), (["B"], "la b es A.a") ],
    [ (["A"], "enchufar PRIM") ],
    [ (["A"], "enchufar a") ],
    [ (["A"], "la X es 1#") ],
    [ (["A"], "un a es bien A bien B") ],
    [ (["A"], "un A es bien a") ],
    [ (["A"], "un A es bien a") ],
    [ (["A"], "un A a es bien A") ], -- should be "A de a"
    [ (["A"], "la a es dado x x") ],
    [ (["A"], "la a es ante x x") ],
    [ (["A"], "la a es ante x da x boludo") ],
    [ (["A"], "la a es ante A da x") ],
    [ (["A"], "la a es ante x da mirar x si (mirar y boludo) da y boludo") ],
    [ (["A"], "encarnar A para a boludo") ],
    [ (["A"], "encarnar A para Bolsa de (a,b) boludo") ],
    [ (["A"], "encarnar A para Bolsa de X boludo") ],
    [ (["A"], "entregar (_) ") ],
    [ (["A"], "enchufar B(_)"), (["B"], "") ],
    -- Sentinel
    [ (["A"], "la a es") ]
  ]

testN :: Int -> TestResult

testN 1 = testMany "TestParser.simpleTestCases"
                   simpleTestCases expected obtained
  where
    expected, obtained :: (String, Declaration) -> Expr
    expected (_, declaration) =
        naLetE [declaration] (naVarE (QualifId globalPackage primMain))
    obtained (string, _) =
        eraseAnnotations $ parseFromStringOrFail
                             globalParserOptions
                             globalPackage primMain string

testN 2 = testMany "TestParser.packageTestCases"
                   packageTestCases expected obtained
  where
    expected, obtained :: ([(PackageName, String)], [Declaration]) -> Expr
    expected (pcs, declarations) =
        naLetE declarations (naVarE (QualifId (mainPackageName pcs) primMain))
    obtained (pcs, _) =
        eraseAnnotations $
        parsePackagesOrFail globalParserOptions
                            (readFromStringsOrFail pcs)
                            primMain
    mainPackageName :: [(PackageName, String)] -> PackageName
    mainPackageName pcs = fst (last (readFromStringsOrFail pcs))

testN 3 = rec 0 packageNonTestCases
  where
    rec _ []          = testOK
    rec i (pcs:tests)
      | canParse pcs =
          testError ("\nFallo el test " ++
                     "(TestParser.packageNonTestCases !! " ++ show i ++ ")" ++
                     "\nTest: " ++ show pcs ++
                     "\nSe esperaba un error de parsing." ++
                     "\nPero se pudo parsear.")
      | otherwise    = rec (i + 1) tests
    canParse :: [(PackageName, String)] -> Bool
    canParse pcs =
      case readFromStrings pcs of
        Left _ -> False
        Right pcs' ->
          case parsePackages globalParserOptions pcs' primMain of
            Left _  -> False
            Right _ -> True

test = mapM_ testN [1..3]

