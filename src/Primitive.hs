
module Primitive(
        primPackage,

        primFixnum, primMinFixnum, primMaxFixnum,
        primChar,
        primString,
        primFunction,
        primTuple,
        primReference,
        primReferenceNew, primReferenceDeref, primReferenceAssign,
        primReferenceEq,

        primContinuation,
        primContinuationCallCC, primContinuationThrow,

        primList, primListNil, primListCons,
        primBool, primBoolTrue, primBoolFalse,
        primError, primErrorMessage, primErrorOK,

        primMonad, primMonadBind, primMonadReturn,
        primDigital, primFromDigits, primToDigits,

        primPutChar,

        primFixnumAdd, primFixnumSub, primFixnumEq, primFixnumLe,
        primFixnumMul, primFixnumDiv, primFixnumMod,
        primFixnumNe, primFixnumLt, primFixnumGe, primFixnumGt,
        primFixnumLshift, primFixnumRshift,
        primFixnumOrb, primFixnumAndb, primFixnumXorb, primFixnumNotb,

        primCharOrd, primCharChr, primSystemExit,

        primTFixnum,
        primTChar,
        primTFloat,
        primTBool,
        primTPtr,
        primTFunction,
        primTContinuation,
        primTTuple,
        primTReference,
        primTString,
        primTError,

        primTList, isPrimTList, primTListContents,
        primPtrPrefix, primPtr, isPrimTPtr, primTPtrDecoration,

        isPrimTFunction, primTFunctionDom, primTFunctionCod,

        primMain, primExports, primBuiltins,
    ) where

import ExpressionE

primPackage :: PackageName
primPackage = ["PRIM"]

primFunction :: Id
primFunction = "Función"

primFixnum :: Id
primFixnum = "Numerito"

primMinFixnum :: Integer
primMinFixnum = 0

primMaxFixnum :: Integer
primMaxFixnum = 2 ^ 32 - 1

primChar :: Id
primChar = "Letra"

primBool :: Id
primBool = "Posta"

primBoolTrue :: Id
primBoolTrue = "Sí"

primBoolFalse :: Id
primBoolFalse = "No"

primError :: Id
primError = "Falible"

primErrorOK :: Id
primErrorOK = "Joya"

primErrorMessage :: Id
primErrorMessage = "Cagó"

primString :: Id
primString = "Texto"

primFloat :: Id
primFloat = "Flotante"

primPtrPrefix :: String
primPtrPrefix = "Pendorcho"

primPtr :: String -> Id
primPtr s = primPtrPrefix ++ " " ++ s

isPrimTPtr :: Type -> Bool
isPrimTPtr (AConstructorT _ (QualifId qualif id)) =
  qualif == primPackage &&
  take (length primPtrPrefix + 1) id == primPtrPrefix ++ " "
isPrimTPtr _ = False

primTPtrDecoration :: Type -> String
primTPtrDecoration (AConstructorT _ (QualifId _ id)) =
  drop (length primPtrPrefix + 1) id

primMonad :: Id
primMonad = "Mónada"

primMonadBind :: Id
primMonadBind = ">>="

primMonadReturn :: Id
primMonadReturn = "fija"

primMonadFail :: Id
primMonadFail = "crepar"

primDigital :: Id
primDigital = "Digital"

primFromDigits :: Id
primFromDigits = "levantar_dígitos"

primToDigits :: Id
primToDigits = "digitalizar"

primTuple :: Int -> Id
primTuple n = "Tupla" ++ show n

primReference :: Id
primReference = "Ref"

primReferenceNew :: Id
primReferenceNew = "Ref"

primReferenceDeref :: Id
primReferenceDeref = "desref"

primReferenceAssign :: Id
primReferenceAssign = "asignar"

primReferenceEq :: Id
primReferenceEq = "igual_ref"

primContinuation :: Id
primContinuation = "Cont"

primContinuationCallCC :: Id
primContinuationCallCC = "ccc"

primContinuationThrow :: Id
primContinuationThrow = "invocar"

primFixnumAdd :: Id
primFixnumAdd = "sumar_numerito"

primFixnumSub :: Id
primFixnumSub = "restar_numerito"

primFixnumEq :: Id
primFixnumEq = "igual_numerito"

primFixnumLe :: Id
primFixnumLe = "menor_o_igual_numerito"

---

primFixnumMul :: Id
primFixnumMul = "multiplicar_numerito"

primFixnumDiv :: Id
primFixnumDiv = "dividir_numerito"

primFixnumMod :: Id
primFixnumMod = "resto_numerito"

primFixnumNe :: Id
primFixnumNe = "distinto_numerito"

primFixnumLt :: Id
primFixnumLt = "menor_numerito"

primFixnumGe :: Id
primFixnumGe = "mayor_o_igual_numerito"

primFixnumGt :: Id
primFixnumGt = "mayor_numerito"

primFixnumLshift :: Id
primFixnumLshift = "mover_izq_numerito"

primFixnumRshift :: Id
primFixnumRshift = "mover_der_numerito"

primFixnumOrb :: Id
primFixnumOrb = "o_numerito"

primFixnumAndb :: Id
primFixnumAndb = "y_numerito"

primFixnumXorb :: Id
primFixnumXorb = "xor_numerito"

primFixnumNotb :: Id
primFixnumNotb = "no_numerito"

primCharOrd :: Id
primCharOrd = "letra_a_numerito"

primCharChr :: Id
primCharChr = "numerito_a_letra"

primSystemExit :: Id
primSystemExit = "espichar"

--

primList :: Id
primList = "Lista"

primListNil :: Id
primListNil = "Vacía"

primListCons :: Id
primListCons = ":"

primPutChar :: Id
primPutChar = "escupir_letra"

primTFunction :: Type -> Type -> Type
primTFunction a b = (con `naAppT` a) `naAppT` b
  where con = naConstructorT (QualifId primPackage primFunction)

primTTuple :: [Type] -> Type
primTTuple ts = foldl naAppT con ts
  where con = naConstructorT (QualifId primPackage (primTuple (length ts)))

primTFixnum :: Type
primTFixnum = naConstructorT (QualifId primPackage primFixnum)

primTChar :: Type
primTChar = naConstructorT (QualifId primPackage primChar)

primTString :: Type
primTString = naConstructorT (QualifId primPackage primString)

primTBool :: Type
primTBool = naConstructorT (QualifId primPackage primBool)

primTFloat :: Type
primTFloat = naConstructorT (QualifId primPackage primFloat)

primTPtr :: String -> Type
primTPtr s = naConstructorT (QualifId primPackage (primPtr s))

primTReference :: Type -> Type
primTReference t =
  naAppT
    (naConstructorT (QualifId primPackage primReference))
    t

primTContinuation :: Type -> Type
primTContinuation t =
  naAppT
    (naConstructorT (QualifId primPackage primContinuation))
    t

primTList :: Type -> Type
primTList t =
  naAppT
    (naConstructorT (QualifId primPackage primList))
    t

isPrimTList :: Type -> Bool
isPrimTList (AAppT _ (AConstructorT _ c) _) =
    c == QualifId primPackage primList
isPrimTList _ = False

primTListContents :: Type -> Type
primTListContents (AAppT _ _ t) = t

primTError :: Type -> Type
primTError t =
  naAppT
    (naConstructorT (QualifId primPackage primError))
    t

primMain :: Id
primMain = "programa"

primExports :: [Id]
primExports = [
    primFunction,
    primFixnum,
    primChar,
    primString,
    primFloat,
    primReference,
    primContinuation,
    primBool,
    primBoolTrue,
    primBoolFalse,
    primList,
    primListNil,
    primListCons,
    primError,
    primErrorMessage,
    primErrorOK,
    primMonad,
    primMonadBind,
    primMonadReturn,
    primMonadFail,
    primDigital,
    primFromDigits,
    primToDigits
  ]

primBuiltins :: [(QualifId, TypeScheme)]
primBuiltins = [
    -- Fixnum arithmetic
    (q primFixnumAdd,
     ForallT [] $ ConstrainedType [] $
     primTFunction primTFixnum (primTFunction primTFixnum primTFixnum)),
    (q primFixnumSub,
     ForallT [] $ ConstrainedType [] $
     primTFunction primTFixnum (primTFunction primTFixnum primTFixnum)),
    (q primFixnumEq,
     ForallT [] $ ConstrainedType [] $
     primTFunction primTFixnum (primTFunction primTFixnum primTBool)),
    (q primFixnumLe,
     ForallT [] $ ConstrainedType [] $
     primTFunction primTFixnum (primTFunction primTFixnum primTBool)),

    (q primFixnumMul,
     ForallT [] $ ConstrainedType [] $
     primTFunction primTFixnum (primTFunction primTFixnum primTFixnum)),
    (q primFixnumDiv,
     ForallT [] $ ConstrainedType [] $
     primTFunction primTFixnum (primTFunction primTFixnum primTFixnum)),
    (q primFixnumMod,
     ForallT [] $ ConstrainedType [] $
     primTFunction primTFixnum (primTFunction primTFixnum primTFixnum)),

    (q primFixnumNe,
     ForallT [] $ ConstrainedType [] $
     primTFunction primTFixnum (primTFunction primTFixnum primTBool)),
    (q primFixnumLt,
     ForallT [] $ ConstrainedType [] $
     primTFunction primTFixnum (primTFunction primTFixnum primTBool)),
    (q primFixnumGe,
     ForallT [] $ ConstrainedType [] $
     primTFunction primTFixnum (primTFunction primTFixnum primTBool)),
    (q primFixnumGt,
     ForallT [] $ ConstrainedType [] $
     primTFunction primTFixnum (primTFunction primTFixnum primTBool)),

    (q primFixnumLshift,
     ForallT [] $ ConstrainedType [] $
     primTFunction primTFixnum (primTFunction primTFixnum primTFixnum)),
    (q primFixnumRshift,
     ForallT [] $ ConstrainedType [] $
     primTFunction primTFixnum (primTFunction primTFixnum primTFixnum)),
    (q primFixnumOrb,
     ForallT [] $ ConstrainedType [] $
     primTFunction primTFixnum (primTFunction primTFixnum primTFixnum)),
    (q primFixnumAndb,
     ForallT [] $ ConstrainedType [] $
     primTFunction primTFixnum (primTFunction primTFixnum primTFixnum)),
    (q primFixnumXorb,
     ForallT [] $ ConstrainedType [] $
     primTFunction primTFixnum (primTFunction primTFixnum primTFixnum)),
    (q primFixnumNotb,
     ForallT [] $ ConstrainedType [] $
     primTFunction primTFixnum primTFixnum),
    -- Characters
    (q primCharOrd,
     ForallT [] $ ConstrainedType [] $
     primTFunction primTChar primTFixnum),
    (q primCharChr,
     ForallT [] $ ConstrainedType [] $
     primTFunction primTFixnum primTChar),
    -- System exit
    (q primSystemExit,
     ForallT [t0] $ ConstrainedType [] $
     primTFunction primTFixnum (naMetavarT t0)),
    -- Continuations
    (q primContinuationCallCC,
     ForallT [t0] $ ConstrainedType [] $
     primTFunction (primTFunction
                       (primTContinuation (naMetavarT t0))
                       (naMetavarT t0))
                   (naMetavarT t0)),
    (q primContinuationThrow,
     ForallT [t0, t1] $ ConstrainedType [] $
     primTFunction (primTContinuation (naMetavarT t0))
                   (primTFunction
                       (naMetavarT t0)
                       (naMetavarT t1))),
    -- References
    (q primReferenceNew,
     ForallT [t0] $ ConstrainedType [] $
     primTFunction (naMetavarT t0)
                   (primTReference (naMetavarT t0))),
    (q primReferenceEq,
     ForallT [t0] $ ConstrainedType [] $
     primTFunction (primTReference (naMetavarT t0))
                   (primTFunction (primTReference (naMetavarT t0))
                                  primTBool)),
    (q primReferenceDeref,
     ForallT [t0] $ ConstrainedType [] $
     primTFunction (primTReference (naMetavarT t0)) (naMetavarT t0)),
    (q primReferenceAssign,
     ForallT [t0] $ ConstrainedType [] $
     primTFunction (primTReference (naMetavarT t0))
                   (primTFunction (naMetavarT t0)
                                  (primTTuple []))),
    -- I/O
    (q primPutChar,
     ForallT [] $ ConstrainedType [] $
     primTFunction primTChar (primTTuple [])),
    -- Constructors
    (q primString,
     ForallT [] $ ConstrainedType [] $
     primTFunction (primTList primTChar) primTString),
    (q primErrorMessage,
     ForallT [t0] $ ConstrainedType [] $
     primTFunction primTString (primTError (naMetavarT t0))),
    (q primErrorOK,
     ForallT [t0] $ ConstrainedType [] $
     primTFunction (naMetavarT t0) (primTError (naMetavarT t0)))
  ]
  where
    q  = QualifId primPackage
    t0 = -1
    t1 = -2

isPrimTFunction :: Type -> Bool
isPrimTFunction (AAppT _ (AAppT _ (AConstructorT _ c) _) _) =
  c == QualifId primPackage primFunction
isPrimTFunction _ = False

primTFunctionDom :: Type -> Type
primTFunctionDom (AAppT _ (AAppT _ _ t) _) = t

primTFunctionCod :: Type -> Type
primTFunctionCod (AAppT _ (AAppT _ _ _) t) = t

