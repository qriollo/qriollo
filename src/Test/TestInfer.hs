
module Test.TestInfer(test) where

import Data.Map as Map(Map, empty, lookup, insert)

import Test.Testing(TestResult, testOK, testError)

import ExpressionE
import Primitive(
        primPackage, primTFixnum, primTFunction, primTTuple, primTList,
        primMain,
    )
import Parser(ParserOptions(..), parseFromString, parseFromStringOrFail)
import Infer(infer, equalModuloRenaming, InferOptions(..))

globalPackage :: PackageName
globalPackage = ["Input"]

globalParserOptions :: ParserOptions
globalParserOptions = ParserOptions {
                        parserOptionsFeatures = []
                      }

infixr 9 -->

(-->) = primTFunction

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

simpleTestCases :: [(String, ConstrainedType)]
simpleTestCases = [
  ("992#", ConstrainedType [] primTFixnum),
  ("(1#,2#,3#)",
   ConstrainedType [] $
   (primTTuple [primTFixnum, primTFixnum, primTFixnum])),
  ("ante x da x",
   ConstrainedType [] (primTFunction (naMetavarT 0) (naMetavarT 0))),
  ("ante x y da x",
   ConstrainedType []
   (primTFunction
        (naMetavarT 0)
        (primTFunction (naMetavarT 1) (naMetavarT 0)))),
  ("ante x y da y",
    ConstrainedType []
    (primTFunction
        (naMetavarT 0)
        (primTFunction (naMetavarT 1) (naMetavarT 1)))),
  ("ante x y da (x,y,x)",
    ConstrainedType []
    (primTFunction
        (naMetavarT 0)
        (primTFunction
            (naMetavarT 1)
            (primTTuple [naMetavarT 0, naMetavarT 1, naMetavarT 0])))),
  ("(ante x da x, ante y da y)",
   ConstrainedType []
    (primTTuple [
        primTFunction (naMetavarT 0) (naMetavarT 0),
        primTFunction (naMetavarT 1) (naMetavarT 1)])),
  ("ante x y da x y",
   ConstrainedType [] $ (t0 --> t1) --> t0 --> t1 ),
  ("(ante k1 x y da k1 x y) (ante x y da y)",
   ConstrainedType [] $ t0 --> t1 --> t1 ),
  ("ante f x y da f y x",
   ConstrainedType [] $ (t0 --> t1 --> t2) --> t1 --> t0 --> t2 ),
  ("ante f g x da f (g x)",
   ConstrainedType [] $ (t0 --> t1) --> (t2 --> t0) --> t2 --> t1 ),
  ("ante f x da f (f x)",
   ConstrainedType [] $ (t0 --> t0) --> t0 --> t0 ),
  ("(ante f x da f x) (ante y da y 1#)",
   ConstrainedType [] $ (int --> t0) --> t0 ),
  ("ante a b da (ante f g x y da (f g, g (g x, y))) (ante g da g (a, b))",
   ConstrainedType [] $
   t0 --> t1 -->
   (primTTuple [t0, t1] --> t0) -->
   primTTuple [t0, t1] --> t1 --> primTTuple [t0, t0]),
  ("ponele que la x es (1#,1#,1#) en x",
   ConstrainedType [] $
   primTTuple [primTFixnum, primTFixnum, primTFixnum]),
  ("ponele que la x es x en x",
   ConstrainedType [] $ t0),
  ("ponele que la f es ante x da f x en f",
   ConstrainedType [] $ t0 --> t1),
  ("ponele que " ++
   "  la f es ante x da g x " ++
   "  la g es ante x da (x, x) " ++
   "  en f",
   ConstrainedType [] $ t0 --> primTTuple [t0, t0]),
  -- Does not require polymorphism:
  ("ponele que " ++
   "  la composición es ante f g x da f (g x) " ++
   "  el duplicar es ante x da (x, x) " ++
   "  el duplicar2 es ante x da (x, x) " ++
   "  en composición duplicar duplicar2 ",
   ConstrainedType [] $ t0 -->
   primTTuple [primTTuple [t0, t0], primTTuple [t0, t0]]),
  -- Requires polymorphism:
  ("ponele que " ++
   "  la composición es ante f g x da f (g x) " ++
   "  el duplicar es ante x da (x, x) " ++
   "  en composición duplicar duplicar ",
   ConstrainedType [] $ t0 -->
   primTTuple [primTTuple [t0, t0], primTTuple [t0, t0]]),
  ("ponele que " ++
   "  la f es ante x da x " ++
   "  en (f 1#, f f) ",
   ConstrainedType [] $ primTTuple [primTFixnum, t0 --> t0]),
  ("ponele que " ++
   "  la identidad es ante x da x " ++
   "  en (identidad, identidad) ",
   ConstrainedType [] $ primTTuple [t0 --> t0, t1 --> t1]),
  -- Primitive recursion encoding for lists
  ("ponele que " ++
   "  la vacía es ante      f z  da  z " ++
   "  la pegar es ante x xs f z  da  f x (xs f z) " ++
   "  en pegar 1# (pegar 2# (pegar 3# vacía)) ",
   ConstrainedType [] $ encList int),
  ("ponele que " ++
   "   el arbitrario      es arbitrario " ++
   "   la vacía           es ante      f z  da  z " ++
   "   el pegar           es ante x xs f z  da  f x (xs f z) " ++
   "   el plegar          es ante f z xs    da  xs f z " ++
   "   el componer        es ante f g x     da  f (g x) " ++
   "   el constantemente  es ante x y       da  x " ++
   " en ponele que " ++ -- force polymorphism for "plegar"
   "   el aplicar         es ante f " ++
   "      da  plegar (componer pegar f) vacía " ++
   "   la cabeza          es plegar constantemente arbitrario " ++
   " en ante z da cabeza (aplicar (ante número da (número, z ())) " ++
   "                              (pegar 1# vacía)) ",
     ConstrainedType [] $ (primTTuple [] --> t0) --> primTTuple [int, t0]),
  -- Interesting case in which we cannot generalize all the variables.
  -- Note that it does NOT have type (t0 --> t1 --> t1).
   ("ante x da " ++
    "  ponele que " ++
    "    el k es ante x y da x " ++
    "    la f es ante y   da (ante g da k (g y) (g x)) " ++
    "                        (ante z da z) " ++
    "  en f ", ConstrainedType [] (t0 --> t0 --> t0)),
  -- sentinel
  ("1#", ConstrainedType [] primTFixnum)
 ]
 where
   t0 = naMetavarT 0
   t1 = naMetavarT 1
   t2 = naMetavarT 2
   int = primTFixnum
   encList a = (a --> t0 --> t0) --> t0 --> t0

programTestCases :: [(String, ConstrainedType)]
programTestCases = [
   (" un A es bien A1 " ++
    " el programa es A1 ",
    ConstrainedType [] $ cons "A" []),
   (" una Lista_ de coso es bien Vacía bien Ag coso (Lista_ de coso) " ++
    " el programa es Vacía ",
    ConstrainedType [] $ cons "Lista_" [t0]),
   (" una Lista_ de coso es bien Vacía bien Ag coso (Lista_ de coso) " ++
    " el programa es Ag ",
    ConstrainedType [] $ t0 --> cons "Lista_" [t0] --> cons "Lista_" [t0]),
   (" una Lista_ de coso es bien Vacía bien Ag coso (Lista_ de coso) " ++
    " el programa es Ag 1#",
    ConstrainedType [] $ cons "Lista_" [int] --> cons "Lista_" [int]),

   (" una Lista_ de coso es bien Vacía bien Ag coso (Lista_ de coso) " ++
    " el programa es Ag 1# (Ag 2# (Ag 3# Vacía))",
    ConstrainedType [] $ cons "Lista_" [int]),
   (" una Lista_ de coso es bien Vacía bien Ag coso (Lista_ de coso) " ++
    " una Posta_ es bien No_ bien Sí_ " ++
    " el programa es (Ag 1# (Ag 2# Vacía), Ag Sí_ (Ag No_ Vacía))",
    ConstrainedType [] $
    primTTuple [
        cons "Lista_" [int],
        cons "Lista_" [cons "Posta_" []]]),
   (" una Lista_ de coso es bien Vacía bien Ag coso (Lista_ de coso) " ++
    " el programa es Ag (Ag 1# Vacía) Vacía",
    ConstrainedType [] $ cons "Lista_" [cons "Lista_" [int]]),
   (" un Par de coso cosito es bien Par coso cosito " ++
    " una Posta_ es bien No_ bien Sí_ " ++
    " el programa es Par 1# (Par 2# Sí_)",
    ConstrainedType [] $ cons "Par" [int, cons "Par" [int, cons "Posta_" []]]),
   (" un AB de a es bien Nil bien Bin (AB de a) a (AB de a) " ++
    " el programa es Bin Nil (ante x da x) Nil",
    ConstrainedType [] $ cons "AB" [t0 --> t0]),
   (" un AB de a es bien Nil bien Bin (AB de a) a (AB de a) " ++
    " el programa es Bin programa 1# programa ",
    ConstrainedType [] $ cons "AB" [int]),
   (" un AB de a es bien Nil bien Bin (AB de a) a (AB de a) " ++
    " una Bolsa de f es bien Bolsa (f de PRIM.Numerito) " ++
    " el programa es Bolsa (Bin Nil 1# Nil)",
    ConstrainedType [] $ cons "Bolsa" [cons "AB" []]),
   (" un Estado de estado valor es bien Estado (estado en (estado, valor)) " ++
    " el programa es Estado (ante x da (x, 1#))",
    ConstrainedType [] $ cons "Estado" [t0, int]),
   (" el x de PRIM.Numerito es 1# " ++
    " el y de PRIM.Numerito en PRIM.Numerito es ante x da x " ++
    " el programa es (x, y) ",
    ConstrainedType [] $ primTTuple [int, int --> int]),
   (" la identidad de a en a es ante x da x " ++
    " el programa es identidad ",
    ConstrainedType [] $ t0 --> t0),
   (" la f de a en a en a es ante x y da x " ++
    " el programa es f ",
    ConstrainedType [] $ t0 --> t0 --> t0),
   -- Lists
   (" una Lista de a es " ++
    " bien Vacía " ++
    " bien : a (Lista de a) " ++
    " el programa es [1#, 2#] ",
    ConstrainedType [] $
    primTList int),
   -- Types do not need to be declared for identifiers to be
   -- polymorphic in nested scopes
   (" el programa es (identidad 1#, identidad (1#, 1#)) " ++
    " donde la identidad es ante x da x boludo ",
    ConstrainedType [] $ primTTuple [int, primTTuple [int, int]]),
   (" el programa es (identidad 1#, identidad (1#, 1#)) " ++
    " donde " ++
    "  la identidad de a en a es " ++
    "  ante x da x " ++
    " boludo ",
    ConstrainedType [] $ primTTuple [int, primTTuple [int, int]]),
   -- But types need to be declared for identifiers to be
   -- polymorphic in the local scope
   (" el programa es (identidad 1#, identidad (1#, 1#)) " ++
    " la identidad de a en a es ante x da x ",
    ConstrainedType [] $ primTTuple [int, primTTuple [int, int]]),
   -- Test pattern matching
   (" el programa dado 1# da 1# ",
    ConstrainedType [] $ int --> int),
   (" el programa es ante x da mirar x " ++
    "     si y da 1#" ++
    "   boludo ",
    ConstrainedType [] $ t0 --> int),
   (" el programa es ante x da mirar x " ++
    "     si (y, z) da y" ++
    "   boludo ",
    ConstrainedType [] $ primTTuple [t0, t1] --> t0),
   (" un AB de a es bien Nil bien Bin (AB de a) a (AB de a) " ++
    " el programa es ante x da mirar x " ++
    "     si Nil        da  0# " ++
    "     si Bin i r d  da  r " ++
    "   boludo ",
    ConstrainedType [] $ cons "AB" [int] --> int),
   (" un AB de a es bien Nil bien Bin (AB de a) a (AB de a) " ++
    " el programa " ++
    "     dado Nil         da  0# " ++
    "     dado (Bin i r d) da  r ",
    ConstrainedType [] $ cons "AB" [int] --> int),
   (" una Posta_ es bien No_ bien Sí_ " ++
    " el programa " ++
    "     dado Sí_ Sí_  da  Sí_ " ++
    "     dado Sí_ No_  da  No_ " ++
    "     dado No_ Sí_  da  No_ " ++
    "     dado No_ No_  da  No_ ",
    ConstrainedType [] $
    (cons "Posta_" [] --> cons "Posta_" [] --> cons "Posta_" [])),
   (" una Posta_ es bien No_ bien Sí_ " ++
    " el programa " ++
    "     dado Sí_ x   da  x  " ++
    "     dado No_ _   da  No_ ",
    ConstrainedType [] $
    (cons "Posta_" [] --> cons "Posta_" [] --> cons "Posta_" [])),
   (" una Posta_ es bien No_ bien Sí_ \n" ++
    " la identidad de cosa en cosa es ante x da x \n" ++
    " el siempre de cosa en cosito en cosa es ante x y da x \n" ++
    " el programa es ante x da mirar x \n" ++
    "     si Sí_ da identidad  \n" ++
    "     si no da siempre No_ \n" ++
    "    boludo ",
    ConstrainedType [] $
    (cons "Posta_" [] --> cons "Posta_" [] --> cons "Posta_" [])),
   (" una Lista_ de coso es bien Vacía bien Ag coso (Lista_ de coso) \n" ++
    " un Nat es bien Cero bien Sucesor Nat \n" ++
    " la longitud de Lista_ de cosa en Nat \n" ++
    "   dada Vacía     da Cero \n" ++
    "   dada (Ag _ xs) da longitud xs \n" ++
    " el programa es longitud (Ag 1# (Ag 2# (Ag 3# Vacía)))\n",
      ConstrainedType [] $ cons "Nat" []),
   (" chirimbolo diestro 10 : " ++
    " una Lista_ de coso es " ++
    "     bien Vacía " ++
    "     bien : coso (Lista_ de coso) \n" ++
    " el aplicar de (coso en cosito) " ++
    "            en Lista_ de coso " ++
    "            en Lista_ de cosito " ++
    "    dadas f Vacía    da Vacía " ++
    "    dadas f (x : xs) da f x : aplicar f xs " ++
    " el siempre dados x y da x " ++
    " el programa " ++
    "   dada lista da " ++
    "        aplicar siempre lista : " ++
    "        aplicar siempre lista : " ++
    "        aplicar siempre lista : " ++
    "        Vacía ",
    ConstrainedType [] $ cons "Lista_" [t0] -->
                         cons "Lista_" [cons "Lista_" [t1 --> t0]]),

   (" el arb de PRIM.Numerito es arb " ++
    " el programa es arb ",
      ConstrainedType [] $ int),

   (" el arb de (PRIM.Numerito, PRIM.Numerito) es arb " ++
    " el programa es arb ",
      ConstrainedType [] $ primTTuple [int, int]),

   -- Typeclasses

   (" cualidad Comparable para coso " ++
    "   el comparar de coso en coso en ()" ++
    " boludo " ++
    " el programa es comparar ",
      ConstrainedType [typeConstraint "Comparable" t0] $
      t0 --> t0 --> primTTuple []),

    (" cualidad Bipunteado para coso " ++
     "   la x de coso " ++
     "   la y de coso " ++
     " boludo " ++
     " encarnar Bipunteado para PRIM.Numerito " ++
     "   la y es 0# " ++
     "   la x es 1# " ++
     " boludo " ++
     " el programa es 1# ",
     ConstrainedType [] $ int),

    (" cualidad A para a " ++
     " boludo " ++
     " encarnar A para (a, b) con (A para a, A para b) " ++
     " boludo " ++
     " el programa es 1# ",
     ConstrainedType [] $ int),

    (" gringo C \"add\" sumar de Numerito en Numerito en Numerito " ++
     " el programa es sumar 1# 2# ",
     ConstrainedType [] $ int),

   -- sentinel
   ("el programa es 1#", ConstrainedType [] primTFixnum)
 ]
 where
   t0 = naMetavarT 0
   t1 = naMetavarT 1
   t2 = naMetavarT 2
   int = primTFixnum
   cons :: Id -> [Type] -> Type
   cons ident = foldl naAppT (naConstructorT (QualifId globalPackage ident))
   class_ :: Id -> QualifId
   class_ ident = QualifId globalPackage ident

programNonTestCases :: [String]
programNonTestCases = [
    " el programa es 1# 2# ",
    " el programa es (ante x da x) 1# 2# ",
    " el programa es (ante x da x, x) ",
    " el programa es (ante f da (f 1#, f ())) (ante x da x) ",
    " el programa es ante x da x x ",

    -- Locally bound identifiers are monomorphic
    " la identidad es ante x da x " ++
    " el programa es (identidad 1#, identidad ()) ",

   -- Return types of case branches do not match
    " una Posta_ es bien No_ bien Sí_ " ++
    " el programa " ++
    " dado Sí_ da Sí_ " ++
    " dado No_ da (ante x da x) ",

   -- Pattern types of case branches do not match
    " una Posta_ es bien No_ bien Sí_ " ++
    " el programa " ++
    " dado Sí_ da Sí_ " ++
    " dado 2#  da No_ ",

   -- Bad type
    " una Lista_ de coso es " ++
    "     bien Cons coso (Lista_ de coso) \n" ++
    " el aplicar de (coso en cosito) " ++
    "            en Lista_ de coso " ++
    "            en Lista_ de cosito " ++
    "    dadas f (Cons x xs) da f x (aplicar f xs)" ++
                           --  ^  note: Cons is missing here
    " el programa es 1# ",

   -- Pattern match against incomplete application of constructor
    " una Lista_ de coso es " ++
    "     bien Cons coso (Lista_ de coso) \n" ++
    " el programa " ++
    " dado (Cons x) da 1# ",

   -- Pattern match against incomplete application of constructor
    " una Lista_ de coso es " ++
    "     bien Cons coso (Lista_ de coso) \n" ++
    " el programa " ++
    " dado (Cons x, z) y da 1# ",

   -- Declared type is too general
   " el arb de coso es 1# " ++
   " el programa es arb ",

   -- Class declared more than once
   " cualidad A para a  boludo " ++
   " cualidad A para a  boludo " ++
   " el programa es 1# ",

   -- Instance of unknown class
   " encarnar A para PRIM.Numerito boludo " ++
   " el programa es 1# ",

   -- Signature of instance does not match signature of class
   " cualidad Bipunteado para coso " ++
   "   la x de a " ++
   "   la y de a " ++
   " boludo " ++
   " encarnar Bipunteado para PRIM.Numerito " ++
   "   la x es 1# " ++
   " boludo " ++
   " el programa es 1# ",

   -- Signature of instance does not match signature of class
   " cualidad Bipunteado para coso " ++
   "   la x de a " ++
   " boludo " ++
   " encarnar Bipunteado para PRIM.Numerito " ++
   "   la x es 1# " ++
   "   la y es 1# " ++
   " boludo " ++
   " el programa es 1# ",

   -- Badly typed
   " cualidad Punteado para coso " ++
   "   la x de a " ++
   " boludo " ++
   " encarnar Punteado para PRIM.Numerito " ++
   "   la x es 1# 1# " ++
   " boludo " ++
   " el programa es 1# ",

   -- Method declaration cannot further constrain the parameter
   " cualidad Igualdad para coso " ++
   "   el igual de coso en coso en coso con Igualdad para coso " ++
   " boludo " ++
   " el programa es igual ",

   -- Implementation of method is not of the right type
   " cualidad Igualdad para coso " ++
   "   el igual de coso en coso en coso " ++
   " boludo " ++
   " encarnar Igualdad para PRIM.Numerito " ++
   "   el igual es 1# " ++
   " boludo " ++
   " el programa es igual ",

   -- Declared method type does not depend on class parameter
   " cualidad Igualdad para coso " ++
   "   el igual de (PRIM.Numerito, a, b) " ++
   " boludo " ++
   " el programa es igual ",

   -- Class restriction for variable not free in the type
   " cualidad Igualdad para coso " ++
   "   el igual de coso en coso en Bool " ++
   " boludo " ++
   " el x de PRIM.Numerito con Igualdad para coso es 1# " ++
   " el programa es x ",

  -- Cannot use "_"
    " el programa dado _ da _ ",

  -- Forbid repeated declarations
    " la x es 1# " ++
    " la x es 1# " ++
    " el programa es 1# ",

  -- Forbid repeated declarations
    " la x es 1# " ++
    " cualidad X para coso " ++
    "   la x de coso " ++
    " boludo " ++
    " el programa es 1# ",

  -- Forbid repeated declarations
    " la x es 1# " ++
    " un X tiene " ++
    "   el x de () " ++
    " boludo " ++
    " el programa es 1# ",

  -- Instance is declared twice
    " cualidad A para a boludo " ++
    " encarnar A para Letra boludo " ++
    " encarnar A para Letra boludo " ++
    " el programa es 1# ",

  -- sentinel
    " el programa es () ()"
  ]

translationTestCases :: [(String, Expr)]
translationTestCases = [
   (" cualidad Igualdad para coso " ++
    "   el igual de coso en coso en coso " ++
    " boludo " ++
    " el programa es 1# ",
    naLetE [
       datatypeD "{data|Igualdad}" ["coso"] [
         constructorDeclaration "{cons|Igualdad}" [
           varT "coso" [] --> varT "coso" [] --> varT "coso" []
         ]
       ],
       valueD "igual" Nothing
              (naLamE primInst
                (naMatchE (naVarE primInst) [
                    MatchBranch (constructorP "{cons|Igualdad}" [
                                   naVarP (primArg 0)
                                ])
                                (naVarE (primArg 0))
                ])), 
       valueD "programa" Nothing (naConstantE (FixnumC 1))
     ]
     (varE "programa")
   ),
 
   (" cualidad Orden para coso " ++
    "   el comp1 de coso en coso en () " ++
    "   el comp2 de coso en coso " ++
    " boludo " ++
    " el programa es 1# ",
    naLetE [
       datatypeD "{data|Orden}" ["coso"] [
         constructorDeclaration "{cons|Orden}" [
           varT "coso" [] --> varT "coso" [] --> primTTuple [],
           varT "coso" [] --> varT "coso" []
         ]
       ],
       valueD "comp1" Nothing
              (naLamE primInst
                (naMatchE (naVarE primInst) [
                    MatchBranch (constructorP "{cons|Orden}" [
                                   naVarP (primArg 0),
                                   naVarP (primArg 1)
                                ])
                                (naVarE (primArg 0))
                ])), 
       valueD "comp2" Nothing
              (naLamE primInst
                (naMatchE (naVarE primInst) [
                    MatchBranch (constructorP "{cons|Orden}" [
                                   naVarP (primArg 0),
                                   naVarP (primArg 1)
                                ])
                                (naVarE (primArg 1))
                ])), 
       valueD "programa" Nothing (naConstantE (FixnumC 1))
     ]
     (varE "programa")
   ),
 
   (" una Posta_ es bien No_ bien Sí_ " ++
    " cualidad Igualdad para coso " ++
    "   el igual de coso en coso en Posta_ " ++
    " boludo " ++
    " el programa es (igual, igual) ",
    naLetE [
       -- classes
       datatypeD "{data|Igualdad}" ["coso"] [
         constructorDeclaration "{cons|Igualdad}" [
           varT "coso" [] --> varT "coso" [] --> constructorT "Posta_" []
         ]
       ],
       valueD "igual" Nothing
              (naLamE primInst
                (naMatchE (naVarE primInst) [
                    MatchBranch (constructorP "{cons|Igualdad}" [
                                   naVarP (primArg 0)
                                ])
                                (naVarE (primArg 0))
                ])), 
       -- instances
       -- datatypes
       datatypeD "Posta_" [] [
         constructorDeclaration "No_" [],
         constructorDeclaration "Sí_" []
       ],
       -- values
       valueD "programa" Nothing
              (naLamE (infer_ 4)
                (naLamE (infer_ 5)
                  (naTupleE [
                    (naAppE (varE "igual") (naVarE $ infer_ 4)),
                    (naAppE (varE "igual") (naVarE $ infer_ 5))
                  ])))
     ]
     (naAppE (naAppE (varE "programa")
                     (naPlaceholderE 2))
             (naPlaceholderE 3))
   ),

  (" una Posta_ es bien No_ bien Sí_ " ++
   " cualidad Igualdad para coso " ++
   "   el igual de coso en coso en Posta_ " ++
   " boludo " ++
   " encarnar Igualdad para PRIM.Numerito " ++
   "   el igual es ante x y da Sí_" ++
   " boludo " ++
   " el programa es igual 2# ",
   naLetE [
      -- classes
      datatypeD "{data|Igualdad}" ["coso"] [
        constructorDeclaration "{cons|Igualdad}" [
          varT "coso" [] --> varT "coso" [] --> constructorT "Posta_" []
        ]
      ],
      valueD "igual" Nothing
             (naLamE primInst
               (naMatchE (naVarE primInst) [
                   MatchBranch (constructorP "{cons|Igualdad}" [
                                  naVarP (primArg 0)
                               ])
                               (naVarE (primArg 0))
               ])),
      -- datatypes
      datatypeD "Posta_" [] [
        constructorDeclaration "No_" [],
        constructorDeclaration "Sí_" []
      ],
      -- instances
      naValueD eq_int Nothing
        (naLamE (QualifId primPackage "_")
          (naAppE (constructorE "{cons|Igualdad}")
                  (lamE "x" (lamE "y" (constructorE "Sí_"))))),
      -- values
      valueD "programa" Nothing
             (naAppE (naAppE (varE "igual")
                             (naAppE (naVarE eq_int) (naTupleE [])))
                     (naConstantE (FixnumC 2)))
    ]
    (varE "programa")
  ),

  (" una Posta_ es bien No_ bien Sí_ " ++
   " una Caja de coso es bien Caja coso " ++
   " cualidad Igualdad para coso " ++
   "   el igual de coso en coso en Posta_ " ++
   " boludo " ++
   " encarnar Igualdad para PRIM.Numerito " ++
   "   el igual es ante x y da Sí_" ++
   " boludo " ++
   " encarnar Igualdad para Caja de a " ++
   "                    con Igualdad para a " ++
   "   el igual " ++
   "      dada (Caja x) (Caja y) da igual x y " ++
   " boludo " ++
   " el programa es igual (Caja 2#) ",
   naLetE [
      -- classes
      datatypeD "{data|Igualdad}" ["coso"] [
        constructorDeclaration "{cons|Igualdad}" [
          varT "coso" [] --> varT "coso" [] --> constructorT "Posta_" []
        ]
      ],
      valueD "igual" Nothing
             (naLamE primInst
               (naMatchE (naVarE primInst) [
                   MatchBranch (constructorP "{cons|Igualdad}" [
                                  naVarP (primArg 0)
                               ])
                               (naVarE (primArg 0))
               ])),
      -- datatypes
      datatypeD "Posta_" [] [
        constructorDeclaration "No_" [],
        constructorDeclaration "Sí_" []
      ],
      datatypeD "Caja" ["coso"] [
        constructorDeclaration "Caja" [varT "coso" []]
      ],
      -- instances
      naValueD eq_int Nothing
        (naLamE (QualifId primPackage "_")
          (naAppE (constructorE "{cons|Igualdad}")
                  (lamE "x" (lamE "y" (constructorE "Sí_"))))),
      naValueD eq_box Nothing
        (naLamE (QualifId primPackage "_")
          (naAppE (constructorE "{cons|Igualdad}")
            (naLamE (infer_ 20)
              (naLamE parser_0 (naLamE parser_1
                (naMatchE
                  (naTupleE [naVarE parser_0,
                             naVarE parser_1])
                  [
                    MatchBranch
                      (naTupleP [constructorP "Caja" [varP "x"],
                                 constructorP "Caja" [varP "y"]])
                      (naAppE
                        (naAppE
                          (naAppE (varE "igual")
                                  (naVarE $ infer_ 20))
                          (varE "x"))
                        (varE "y"))
                  ])))))),
      -- values
      valueD "programa" Nothing
             (naAppE (naAppE (varE "igual")
                             (naAppE (naAppE (naVarE eq_box) (naTupleE []))
                                     (naAppE (naVarE eq_int) (naTupleE []))))
                     (naAppE
                       (constructorE "Caja")
                       (naConstantE (FixnumC 2))))
    ]
    (varE "programa")
   ),

   (" una Posta_ es bien No_ bien Sí_ " ++
    " cualidad Igualdad para coso " ++
    "   el igual de coso en coso en Posta_ " ++
    " boludo " ++
    " encarnar Igualdad para PRIM.Numerito " ++
    "   el igual es ante x y da Sí_" ++
    " boludo " ++
    " el programa es ante x da igual x x ",
    naLetE [
       -- classes
       datatypeD "{data|Igualdad}" ["coso"] [
         constructorDeclaration "{cons|Igualdad}" [
           varT "coso" [] --> varT "coso" [] --> constructorT "Posta_" []
         ]
       ],
       valueD "igual" Nothing
              (naLamE primInst
                (naMatchE (naVarE primInst) [
                    MatchBranch (constructorP "{cons|Igualdad}" [
                                   naVarP (primArg 0)
                                ])
                                (naVarE (primArg 0))
                ])),
       -- datatypes
       datatypeD "Posta_" [] [
         constructorDeclaration "No_" [],
         constructorDeclaration "Sí_" []
       ],
       -- instances
       naValueD eq_int Nothing
         (naLamE (QualifId primPackage "_")
           (naAppE (constructorE "{cons|Igualdad}")
                   (lamE "x" (lamE "y" (constructorE "Sí_"))))),
       -- values
       valueD "programa" Nothing
              (naLamE (infer_ 8)
                (lamE "x"
                  (naAppE
                    (naAppE (naAppE (varE "igual") (naVarE $ infer_ 8))
                            (varE "x"))
                    (varE "x"))))
     ]
     (naAppE (varE "programa") (naPlaceholderE 1)) 
   ),

   (" una Posta_ es bien No_ bien Sí_ " ++
    " cualidad Igualdad para coso " ++
    "   el igual de coso en coso en Posta_ " ++
    " boludo " ++
    " encarnar Igualdad para PRIM.Numerito " ++
    "   el igual es ante x y da Sí_" ++
    " boludo " ++
    " el programa de coso en Posta_ " ++
    "                         con Igualdad para coso " ++
    " es ante x da igual x x ",
    naLetE [
       -- classes
       datatypeD "{data|Igualdad}" ["coso"] [
         constructorDeclaration "{cons|Igualdad}" [
           varT "coso" [] --> varT "coso" [] --> constructorT "Posta_" []
         ]
       ],
       valueD "igual" Nothing
              (naLamE primInst
                (naMatchE (naVarE primInst) [
                    MatchBranch (constructorP "{cons|Igualdad}" [
                                   naVarP (primArg 0)
                                ])
                                (naVarE (primArg 0))
                ])),
       -- datatypes
       datatypeD "Posta_" [] [
         constructorDeclaration "No_" [],
         constructorDeclaration "Sí_" []
       ],
       -- instances
       naValueD eq_int Nothing
         (naLamE (QualifId primPackage "_")
           (naAppE (constructorE "{cons|Igualdad}")
                   (lamE "x" (lamE "y" (constructorE "Sí_"))))),
       -- values
       valueD "programa"
              (Just (ConstrainedType
                        [typeConstraint "Igualdad" (varT "coso" [])]
                        (varT "coso" [] --> constructorT "Posta_" [])))
              (naLamE (infer_ 8) 
                (lamE "x"
                  (naAppE
                    (naAppE (naAppE (varE "igual") (naVarE $ infer_ 8))
                            (varE "x"))
                    (varE "x"))))

     ]
     (naAppE (varE "programa") (naPlaceholderE 1)) 
   ),

   (" una Posta_ es bien No_ bien Sí_ " ++
    " cualidad Igualdad para coso " ++
    "   el igual de coso en coso en Posta_ " ++
    " boludo " ++
    " encarnar Igualdad para PRIM.Numerito " ++
    "   el igual es ante x y da Sí_" ++
    " boludo " ++
    " el programa de PRIM.Numerito en Posta_ " ++
    " es ante x da igual x x ",
    naLetE [
       -- classes
       datatypeD "{data|Igualdad}" ["coso"] [
         constructorDeclaration "{cons|Igualdad}" [
           varT "coso" [] --> varT "coso" [] --> constructorT "Posta_" []
         ]
       ],
       valueD "igual" Nothing
              (naLamE primInst
                (naMatchE (naVarE primInst) [
                    MatchBranch (constructorP "{cons|Igualdad}" [
                                   naVarP (primArg 0)
                                ])
                                (naVarE (primArg 0))
                ])),
       -- datatypes
       datatypeD "Posta_" [] [
         constructorDeclaration "No_" [],
         constructorDeclaration "Sí_" []
       ],
       -- instances
       naValueD eq_int Nothing
         (naLamE (QualifId primPackage "_")
           (naAppE (constructorE "{cons|Igualdad}")
                   (lamE "x" (lamE "y" (constructorE "Sí_"))))),
       -- values
       valueD "programa"
              (Just (ConstrainedType []
                        (int --> constructorT "Posta_" [])))
                (lamE "x"
                  (naAppE
                    (naAppE (naAppE (varE "igual")
                                    (naAppE (naVarE eq_int) (naTupleE [])))
                            (varE "x"))
                    (varE "x")))

     ]
     (varE "programa")
   ),

  -- sentinel
    (" el programa es () ",
     naLetE [ valueD "programa" Nothing (naTupleE []) ]
            (varE "programa")
    )
  ]
  where
    int = primTFixnum
    primInst  = QualifId primPackage "{inst}"
    primArg i = QualifId primPackage ("{m|" ++ show i ++ "}")
    eq_int = QualifId primPackage "{inst|Input.Igualdad|PRIM.Numerito}"
    eq_box = QualifId primPackage "{inst|Input.Igualdad|Input.Caja}"
    parser_0 = QualifId primPackage "{parser|0}"
    parser_1 = QualifId primPackage "{parser|1}"
    infer_ n = QualifId primPackage ("{infer|" ++ show n ++ "}")

testN :: Int -> TestResult
testN 1 = rec 0 simpleTestCases
  where
    rec _ [] = testOK
    rec i ((string, expected):ts)
      | obtained `equalModuloRenaming` expected = rec (i + 1) ts
      | otherwise =
        testError ("\nFallo el test " ++
                   "(TestInfer.simpleTestCases !! " ++ show i ++ ")" ++
                   "\nAl tipar: " ++ show string ++
                   "\nEsperado: " ++ show (eraseAnnotations expected) ++
                   "\nObtenido: " ++ show (eraseAnnotations obtained))
      where obtained :: ConstrainedType
            obtained = snd $ inferStringOrFail string

testN 2 = rec 0 programTestCases
  where
    rec _ [] = testOK
    rec i ((string, expected):ts)
      | obtained `equalModuloRenaming` expected = rec (i + 1) ts
      | otherwise =
        testError ("\nFallo el test " ++
                   "(TestInfer.programTestCases !! " ++ show i ++ ")" ++
                   "\nAl tipar: " ++ show string ++
                   "\nEsperado: " ++ show (eraseAnnotations expected) ++
                   "\nObtenido: " ++ show (eraseAnnotations obtained))
      where obtained :: ConstrainedType
            obtained = snd $ inferProgramOrFail string 

testN 3 = rec 0 programNonTestCases
  where
    rec _ [] = testOK
    rec i (string : ts)
      | canInferTypeFor string =
        testError ("\nFallo el test " ++
                   "(TestInfer.programNonTestCases !! " ++ show i ++ ")" ++
                   "\nAl tipar: " ++ show string ++
                   "\nSe esperaba no poder tiparlo, pero se pudo tipar.")
      | otherwise = rec (i + 1) ts
      where canInferTypeFor :: String -> Bool
            canInferTypeFor string = do
              case parseFromString globalParserOptions
                                   globalPackage primMain string of
                Left _ -> error ("El test de tipado es una expresión " ++
                                 "sintácticamente mal formada " ++
                                 "(no sirve como test de inferencia).")
                Right _ -> case inferProgram string of
                             Left _  -> False
                             Right _ -> True

testN 4 = rec 0 translationTestCases
  where
    rec _ [] = testOK
    rec i ((string, expected) : ts)
      | eraseAnnotations expected == eraseAnnotations obtained =
        rec (i + 1) ts
      | otherwise =
        testError ("\nFallo el test " ++
                   "(TestInfer.translationTestCases !! " ++ show i ++ ")" ++
                   "\nAl tipar: " ++ show string ++
                   "\nEsperado: " ++ show (eraseAnnotations expected) ++
                   "\nObtenido: " ++ show (eraseAnnotations obtained))
      where
        obtained :: Expr
        obtained = fst . inferProgramOrFail $ string 

test :: TestResult
test = mapM_ testN [1..4]

orFail :: Either String a -> a
orFail e = case e of
             Right x  -> x
             Left msg -> error msg

inferStringOrFail :: String -> (Expr, ConstrainedType)
inferStringOrFail string =
  case infer EnforceValueRestriction . parseAtomicExpression $ string of
    Left msg  -> error msg
    Right res -> res
  where
    parseAtomicExpression :: String -> Expr
    parseAtomicExpression string =
        let ALetE _ [AValueD _ _ _ e] _ =
              parseFromStringOrFail globalParserOptions
                                    globalPackage primMain
                                    ("el programa es " ++ string)
         in e

inferProgram :: String -> Either String (Expr, ConstrainedType)
inferProgram string = do
  expr <- parseFromString globalParserOptions
                          globalPackage
                          primMain
                          string
  infer EnforceValueRestriction expr

inferProgramOrFail :: String -> (Expr, ConstrainedType)
inferProgramOrFail string = orFail (inferProgram string)

