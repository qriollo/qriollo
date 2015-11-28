
module Backend.C(compileToC) where

import qualified Data.Map as Map(Map, empty, insert, lookup, fromList)

import Control.Monad(zipWithM)
import Control.Monad.Trans.State.Lazy(State, get, modify, evalState)
import Data.List(sort, nub, union, (\\))
import Data.Char(ord)

import ExpressionE
import ExpressionL
import ExpressionK
import Backend.C_MM(memoryManager)

type CCode = String
data CState = CState {
                cstCurrentFunction :: Maybe IdK,
                cstFunctionFormals :: Map.Map IdK [IdK]
              }
type CM = State CState

base :: Integer -> Integer -> String
base b 0 = "0"
base b n = rec b n
  where
    alphabet :: String
    alphabet =
      "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
    rec :: Integer -> Integer -> String
    rec b 0 = []
    rec b n = rec b (n `div` b) ++ [alphabet !! fromIntegral (n `mod` b)]

mangle :: Integer -> String
mangle = base 62

length' :: [a] -> Integer
length' = fromIntegral . length

reachableRegisterFlags :: [IdK] -> Integer
reachableRegisterFlags regs = sum $ map (\ r -> 2 ^ r) regs

compileToC :: [Pragma] -> ExprK -> CCode
compileToC pragmas expr = evalState (compileProgram expr) initialState
  where
    initialState :: CState
    initialState = CState {
                     cstCurrentFunction = Nothing,
                     cstFunctionFormals = Map.fromList [
                       -- Toplevel continuation
                       (-1, [0])
                     ]
                   }

    compileProgram :: ExprK -> CM CCode
    compileProgram expr = do
      exprCode   <- compileExpr expr
      headerCode <- header
      footerCode <- footer
      return $ headerCode ++
               pragmasCode ++
               exprCode ++
               footerCode

    mangleLabel :: IdK -> CCode
    mangleLabel (-1)  = "qr_top"
    mangleLabel label = "qr_L_" ++ mangle label 

    mangleVar :: IdK -> CCode
    mangleVar i = "qr_reg[" ++ show i ++ "]"

    pragmasCode :: CCode
    pragmasCode = let code = concatMap pragmaCode pragmas in
                    if null code
                     then ""
                     else "/* User pragmas */\n" ++ code ++ "\n"
      where
        pragmaCode (ForeignPragma ForeignLangC str) = str ++ "\n"
        pragmaCode (ForeignPragma lang _) =
          error ("compileToC: lenguaje gringo no soportado: " ++
                 show lang ++ ")")

    header :: CM CCode
    header = return $
             unlines $ [
               "#include <stdio.h>",
               "#include <stdlib.h>",
               "#include <locale.h>",
               "#include <wchar.h>",
               "#include <string.h>",
               "",
               "typedef unsigned long long u64;",
               "typedef unsigned long long QrObj;",
               "typedef unsigned int QrFixnum;",
               "typedef void (QrCont)(void);",
               "",
               "#define Qr_CONT(F) " ++
               "__attribute__((aligned)) " ++
               "void F(void)",
               "",
               "/* Helper macros */",
               "#define Qr_CONT_AS_OBJ(X)   (((QrObj)(X)) | 1)",
               "#define Qr_OBJ_AS_CONT(X)   (*(QrCont *)((X) & ~(QrObj)1))",
               "#define Qr_PTR_AS_OBJ(X)    (((QrObj)(X)) | 1)",
               "#define Qr_OBJ_AS_PTR(X)    (*(QrCont *)((X) & ~(QrObj)1))",
               "#define Qr_RECORD_AS_OBJ(X) ((QrObj)(X))",
               "#define Qr_OBJ_AS_RECORD(X) ((QrObj *)(X))",
               "#define Qr_FIXNUM_AS_OBJ(X) (((QrObj)(X) << 1) | 1)",
               "#define Qr_OBJ_AS_FIXNUM(X) ((QrFixnum)((X) >> 1))",
               "#define Qr_OBJ_TAG(X) (((X) & 1) ? (X) : ((QrObj *)(X))[1])",
               "#define Qr_OBJ_IMMEDIATE(X) ((X) & 1)",
               "#define Qr_OBJ_BOXED(X)     (!Qr_OBJ_IMMEDIATE((X)))",
               "",
               "/* Machine registers */",
               "QrObj qr_cont;",
               "#define Qr_NREGISTERS " ++ show numRegisters,
               "QrObj qr_reg[Qr_NREGISTERS];",
               "",
               "/* Forward declarations */",
               "void qr_start(void);",
               "void qr_top(void);"
               ] ++
               map (\ label -> "void " ++ mangleLabel label ++ "(void);")
                   (definedLabels expr) ++
               [
               "",
               memoryManager
               ]

    numRegisters :: Integer
    numRegisters = maximum (usedRegisters expr) + 1

    usedRegisters :: ExprK -> [IdK]
    usedRegisters expr =
      ((sort (nub (allIds expr)) \\ [-1]) \\ definedLabels expr)
      `union`
      [0]
      
             

    footer :: CM CCode
    footer = return $
      unlines [
        "",
        "int main() {",
        "    setlocale(LC_ALL, \"en_US.UTF-8\");",
        "    qr_mm_init();",
        "    qr_cont = Qr_CONT_AS_OBJ(qr_start);",
        "    for (;;) {",
        "        Qr_OBJ_AS_CONT(qr_cont)();",
        "    }",
        "    return 0;",
        "}",
        ""
      ]

    definedLabels :: ExprK -> [IdK]
    definedLabels (LetK decls _) = map declLabel decls
      where
        declLabel :: DeclarationK -> IdK
        declLabel (ValueDK label _ _) = label
    definedLabels _ = []

    compileExpr :: ExprK -> CM CCode
    compileExpr (RecordK vals id expr) = do
      setVals <- zipWithM setVal [1..] vals
      exprCode <- compileExpr expr
      let sizeU64 = 1 + length' vals in
        if length' vals == 0
         then
           error "(compileToC: no se puede crear un registro de 0 elementos)"
         else do
           return $
             "    {\n" ++
             "        QrObj *rec;\n" ++
             "        Qr_MM_ALLOC(rec, " ++ show sizeU64 ++ ");\n" ++
             "        rec[0] = Qr_RECORD_TAG(" ++ show sizeU64 ++ ");\n" ++
             concat setVals ++
             "        " ++ mangleVar id ++ " = Qr_RECORD_AS_OBJ(rec);\n" ++
             "    }\n" ++
             exprCode
      where
        setVal :: Integer -> ValueK -> CM CCode
        setVal i val = do
          valCode <- compileV val
          return $ "        rec[" ++ show i ++ "] = " ++ valCode ++
                   ";\n"
    compileExpr (SelectK n val id expr) = do
      valCode <- compileV val
      exprCode <- compileExpr expr
      return $
        "    " ++ mangleVar id ++ " = Qr_OBJ_AS_RECORD(" ++ valCode ++ ")" ++
                                  "[" ++ show (n + 1) ++ "];\n" ++
        exprCode
    compileExpr (AppK val vals) = do
        valCode          <- compileV val
        functionFormals  <- getFunctionFormals val (length' vals)
        let valsFormals2 = filter
                             (\ (val, formal) -> val /= VarK formal)
                             (zip vals functionFormals)
            vals2    = map fst valsFormals2
            formals2 = map snd valsFormals2
         in do
           setParamValues   <- zipWithM setParamValue [1..] vals2
           setParamInRecord <- zipWithM setParamInRecord [1..] formals2
           selfCall <- isSelfCall val
           return $ "    {\n" ++
                    concat setParamValues ++
                    (if selfCall
                     then ""
                     else "        qr_cont = " ++ valCode ++ ";\n") ++
                    concat setParamInRecord ++
                    "    }\n" ++
                    (if selfCall
                      then "    goto " ++ initLabel val ++ ";\n"
                      else "    return;\n")
      where
        setParamValue :: Integer -> ValueK -> CM CCode
        setParamValue i val = do
          valCode <- compileV val
          return $ "        QrObj p_" ++ show i ++ " = " ++ valCode ++ ";\n"
        setParamInRecord :: Integer -> IdK -> CM CCode
        setParamInRecord i var = do
          return $ "        " ++ mangleVar var ++ " = p_" ++ show i ++ ";\n"
        isSelfCall :: ValueK -> CM Bool
        isSelfCall (LabelK f) = do
          state <- get
          return $ cstCurrentFunction state == Just f
        isSelfCall _ = return False
        initLabel (LabelK f) = mangleLabel f ++ "_init"
    compileExpr (LetK decls expr) = do
        mapM_ declareFunction decls
        declsCode <- mapM compileDecl decls

        modify (\ state -> state { cstCurrentFunction = Nothing })
        exprCode  <- compileExpr expr
        return $
          "\n/* Function declarations */\n" ++
          concat declsCode ++
          "\n" ++
          "Qr_CONT(qr_top) {\n" ++
          --"    printf(\"%llu\\n\", qr_reg[0]);\n" ++
          "    qr_mm_end();\n" ++
          "    exit(0);\n" ++
          "}\n" ++
          "\n" ++
          "Qr_CONT(qr_start) {\n" ++
          exprCode ++
          "}\n"
      where
        declareFunction :: DeclarationK -> CM ()
        declareFunction (ValueDK label params _) =
          modify (\ state -> state {
            cstFunctionFormals =
              Map.insert label
                         params
                         (cstFunctionFormals state)
          })

        compileDecl :: DeclarationK -> CM CCode
        compileDecl (ValueDK label params body) = do
          modify (\ state -> state {
            cstCurrentFunction = Just label
          })
          bodyCode <- compileExpr body
          return $
            "\n" ++
            "Qr_CONT(" ++ mangleLabel label ++ ") {\n" ++
            (if callsSelf label body
             then mangleLabel label ++ "_init:\n"
             else "") ++
            "    if (Qr_MM_SHOULD_GC()) {\n" ++
            "       qr_mm_gc(" ++
            show (reachableRegisterFlags params) ++ ");\n" ++
            "    }\n" ++
            bodyCode ++
            "}\n"
    compileExpr (SwitchK val exprs) = do
        valCode <- compileV val
        exprsCode <- zipWithM compileBranch [0..] exprs
        return $
          "    switch (Qr_OBJ_AS_FIXNUM(" ++ valCode ++ ")) {\n" ++
          concat exprsCode ++
          "    }\n"
      where
        compileBranch :: Integer -> ExprK -> CM CCode
        compileBranch n expr = do
          exprCode <- compileExpr expr
          return $
            "    case " ++ show n ++ ":\n" ++ indent exprCode
    compileExpr (PrimitiveK PrimRef [val] [id] [expr]) =
      compileExpr (RecordK [val] id expr)
    compileExpr (PrimitiveK PrimDeref [val] [id] [expr]) =
      compileExpr (SelectK 0 val id expr)
    compileExpr (PrimitiveK PrimAssign [vref, vval] mId [expr]) = do
      vrefCode <- compileV vref
      vvalCode <- compileV vval
      exprCode <- compileExpr expr
      return $ "    Qr_OBJ_AS_RECORD(" ++ vrefCode ++ ")[1] = " ++
                                          vvalCode ++ ";\n" ++
               assignUnit mId ++
               exprCode
    compileExpr (PrimitiveK PrimTag [val] [id] [expr]) = do
      valCode  <- compileV val
      exprCode <- compileExpr expr
      return $ "    " ++ mangleVar id ++ " = " ++
               "Qr_OBJ_TAG(" ++ valCode ++ ");\n" ++
               exprCode
    compileExpr (PrimitiveK PrimBoxed [val] [] [expr1, expr2]) = do
      valCode  <- compileV val
      expr1Code <- compileExpr expr1
      expr2Code <- compileExpr expr2
      return $ "    if (Qr_OBJ_BOXED(" ++ valCode ++ ")) {\n" ++
               indent expr1Code ++
               "    } else {\n" ++
               indent expr2Code ++
               "    }\n"
    compileExpr (PrimitiveK PrimFixnumAdd [val1, val2] [id] [expr]) = do
      val1Code <- compileV val1
      val2Code <- compileV val2
      exprCode <- compileExpr expr
      return $ "    " ++ mangleVar id ++ " = " ++
               val1Code ++ " + " ++ val2Code ++ " - 1;\n" ++
               exprCode
    compileExpr (PrimitiveK PrimFixnumSub [val1, val2] [id] [expr]) = do
      val1Code <- compileV val1
      val2Code <- compileV val2
      exprCode <- compileExpr expr
      return $ "    " ++ mangleVar id ++ " = " ++
               val1Code ++ " - " ++ val2Code ++ " + 1;\n" ++
               exprCode
    compileExpr (PrimitiveK PrimFixnumEq [val1, val2] [] [expr1, expr2]) = do
      val1Code <- compileV val1
      val2Code <- compileV val2
      expr1Code <- compileExpr expr1
      expr2Code <- compileExpr expr2
      return $ "    if (" ++
               "Qr_OBJ_AS_FIXNUM(" ++ val1Code ++ ") == " ++
               "Qr_OBJ_AS_FIXNUM(" ++ val2Code ++ ")" ++
               ") {\n" ++
               indent expr1Code ++
               "    } else {\n" ++
               indent expr2Code ++
               "    }\n"
    compileExpr (PrimitiveK PrimFixnumLe [val1, val2] [] [expr1, expr2]) = do
      val1Code <- compileV val1
      val2Code <- compileV val2
      expr1Code <- compileExpr expr1
      expr2Code <- compileExpr expr2
      return $ "    if (" ++
               "Qr_OBJ_AS_FIXNUM(" ++ val1Code ++ ") <= " ++
               "Qr_OBJ_AS_FIXNUM(" ++ val2Code ++ ")" ++
               ") {\n" ++
               indent expr1Code ++
               "    } else {\n" ++
               indent expr2Code ++
               "    }\n"

    compileExpr (PrimitiveK PrimFixnumMul [val1, val2] [id] [expr]) = do
      val1Code <- compileV val1
      val2Code <- compileV val2
      exprCode <- compileExpr expr
      return $ "    " ++ mangleVar id ++ " = " ++
               "Qr_FIXNUM_AS_OBJ(" ++
               "Qr_OBJ_AS_FIXNUM(" ++ val1Code ++ ")" ++
               " * " ++
               "Qr_OBJ_AS_FIXNUM(" ++ val2Code ++ "));\n" ++
               exprCode

    compileExpr (PrimitiveK PrimFixnumDiv [val1, val2] [id] [expr]) = do
      val1Code <- compileV val1
      val2Code <- compileV val2
      exprCode <- compileExpr expr
      return $ "    " ++ mangleVar id ++ " = " ++
               "Qr_FIXNUM_AS_OBJ(" ++
               "Qr_OBJ_AS_FIXNUM(" ++ val1Code ++ ")" ++
               " / " ++
               "Qr_OBJ_AS_FIXNUM(" ++ val2Code ++ "));\n" ++
               exprCode

    compileExpr (PrimitiveK PrimFixnumMod [val1, val2] [id] [expr]) = do
      val1Code <- compileV val1
      val2Code <- compileV val2
      exprCode <- compileExpr expr
      return $ "    " ++ mangleVar id ++ " = " ++
               "Qr_FIXNUM_AS_OBJ(" ++
               "Qr_OBJ_AS_FIXNUM(" ++ val1Code ++ ")" ++
               " % " ++
               "Qr_OBJ_AS_FIXNUM(" ++ val2Code ++ "));\n" ++
               exprCode

    compileExpr (PrimitiveK PrimFixnumLt [val1, val2] [] [expr1, expr2]) = do
      val1Code <- compileV val1
      val2Code <- compileV val2
      expr1Code <- compileExpr expr1
      expr2Code <- compileExpr expr2
      return $ "    if (" ++
               "Qr_OBJ_AS_FIXNUM(" ++ val1Code ++ ") < " ++
               "Qr_OBJ_AS_FIXNUM(" ++ val2Code ++ ")" ++
               ") {\n" ++
               indent expr1Code ++
               "    } else {\n" ++
               indent expr2Code ++
               "    }\n"

    compileExpr (PrimitiveK PrimFixnumNe [val1, val2] [] [expr1, expr2]) = do
      val1Code <- compileV val1
      val2Code <- compileV val2
      expr1Code <- compileExpr expr1
      expr2Code <- compileExpr expr2
      return $ "    if (" ++
               "Qr_OBJ_AS_FIXNUM(" ++ val1Code ++ ") != " ++
               "Qr_OBJ_AS_FIXNUM(" ++ val2Code ++ ")" ++
               ") {\n" ++
               indent expr1Code ++
               "    } else {\n" ++
               indent expr2Code ++
               "    }\n"

    compileExpr (PrimitiveK PrimFixnumGe [val1, val2] [] [expr1, expr2]) = do
      val1Code <- compileV val1
      val2Code <- compileV val2
      expr1Code <- compileExpr expr1
      expr2Code <- compileExpr expr2
      return $ "    if (" ++
               "Qr_OBJ_AS_FIXNUM(" ++ val1Code ++ ") >= " ++
               "Qr_OBJ_AS_FIXNUM(" ++ val2Code ++ ")" ++
               ") {\n" ++
               indent expr1Code ++
               "    } else {\n" ++
               indent expr2Code ++
               "    }\n"

    compileExpr (PrimitiveK PrimFixnumGt [val1, val2] [] [expr1, expr2]) = do
      val1Code <- compileV val1
      val2Code <- compileV val2
      expr1Code <- compileExpr expr1
      expr2Code <- compileExpr expr2
      return $ "    if (" ++
               "Qr_OBJ_AS_FIXNUM(" ++ val1Code ++ ") > " ++
               "Qr_OBJ_AS_FIXNUM(" ++ val2Code ++ ")" ++
               ") {\n" ++
               indent expr1Code ++
               "    } else {\n" ++
               indent expr2Code ++
               "    }\n"

    compileExpr (PrimitiveK PrimFixnumLshift [val1, val2] [id] [expr]) = do
      val1Code <- compileV val1
      val2Code <- compileV val2
      exprCode <- compileExpr expr
      return $ "    " ++ mangleVar id ++ " = " ++
               "Qr_FIXNUM_AS_OBJ(" ++
               "Qr_OBJ_AS_FIXNUM(" ++ val1Code ++ ")" ++
               " << " ++
               "Qr_OBJ_AS_FIXNUM(" ++ val2Code ++ "));\n" ++
               exprCode

    compileExpr (PrimitiveK PrimFixnumRshift [val1, val2] [id] [expr]) = do
      val1Code <- compileV val1
      val2Code <- compileV val2
      exprCode <- compileExpr expr
      return $ "    " ++ mangleVar id ++ " = " ++
               "Qr_FIXNUM_AS_OBJ(" ++
               "Qr_OBJ_AS_FIXNUM(" ++ val1Code ++ ")" ++
               " >> " ++
               "Qr_OBJ_AS_FIXNUM(" ++ val2Code ++ "));\n" ++
               exprCode

    compileExpr (PrimitiveK PrimFixnumOrb [val1, val2] [id] [expr]) = do
      val1Code <- compileV val1
      val2Code <- compileV val2
      exprCode <- compileExpr expr
      return $ "    " ++ mangleVar id ++ " = " ++
               "Qr_FIXNUM_AS_OBJ(" ++
               "Qr_OBJ_AS_FIXNUM(" ++ val1Code ++ ")" ++
               " | " ++
               "Qr_OBJ_AS_FIXNUM(" ++ val2Code ++ "));\n" ++
               exprCode

    compileExpr (PrimitiveK PrimFixnumAndb [val1, val2] [id] [expr]) = do
      val1Code <- compileV val1
      val2Code <- compileV val2
      exprCode <- compileExpr expr
      return $ "    " ++ mangleVar id ++ " = " ++
               "Qr_FIXNUM_AS_OBJ(" ++
               "Qr_OBJ_AS_FIXNUM(" ++ val1Code ++ ")" ++
               " & " ++
               "Qr_OBJ_AS_FIXNUM(" ++ val2Code ++ "));\n" ++
               exprCode

    compileExpr (PrimitiveK PrimFixnumXorb [val1, val2] [id] [expr]) = do
      val1Code <- compileV val1
      val2Code <- compileV val2
      exprCode <- compileExpr expr
      return $ "    " ++ mangleVar id ++ " = " ++
               "Qr_FIXNUM_AS_OBJ(" ++
               "Qr_OBJ_AS_FIXNUM(" ++ val1Code ++ ")" ++
               " ^ " ++
               "Qr_OBJ_AS_FIXNUM(" ++ val2Code ++ "));\n" ++
               exprCode

    compileExpr (PrimitiveK PrimFixnumNotb [val1] [id] [expr]) = do
      val1Code <- compileV val1
      exprCode <- compileExpr expr
      return $ "    " ++ mangleVar id ++ " = " ++
               "Qr_FIXNUM_AS_OBJ(" ++
               "~Qr_OBJ_AS_FIXNUM(" ++ val1Code ++ "));\n" ++
               exprCode

    compileExpr (PrimitiveK PrimCharOrd [val] [id] [expr]) = do
      valCode  <- compileV val
      exprCode <- compileExpr expr
      return $ "    " ++ mangleVar id ++ " = " ++ valCode ++ ";\n" ++
               exprCode

    compileExpr (PrimitiveK PrimCharChr [val] [id] [expr]) = do
      valCode  <- compileV val
      exprCode <- compileExpr expr
      return $ "    " ++ mangleVar id ++ " = " ++ valCode ++ ";\n" ++
               exprCode

    compileExpr (PrimitiveK PrimReferenceEq [val1, val2] [] [expr1, expr2]) = do
      val1Code <- compileV val1
      val2Code <- compileV val2
      expr1Code <- compileExpr expr1
      expr2Code <- compileExpr expr2
      return $ "    if (" ++
               "Qr_OBJ_AS_PTR(" ++ val1Code ++ ") == " ++
               "Qr_OBJ_AS_PTR(" ++ val2Code ++ ")" ++
               ") {\n" ++
               indent expr1Code ++
               "    } else {\n" ++
               indent expr2Code ++
               "    }\n"

    compileExpr (PrimitiveK PrimSystemExit [val] [id] [expr]) = do
      valCode  <- compileV val
      exprCode <- compileExpr expr
      return $ "    exit(Qr_OBJ_AS_FIXNUM(" ++ valCode ++ "));\n" ++
               exprCode

    compileExpr (PrimitiveK PrimPutChar [val] mId [expr]) = do
      valCode  <- compileV val
      exprCode <- compileExpr expr
      return $ "    putwchar(Qr_OBJ_AS_FIXNUM(" ++ valCode ++ "));\n" ++
               assignUnit mId ++
               exprCode
    compileExpr (PrimitiveK _ _ _ _) =
      error "(compileToC: primitiva no implementada)"

    compileExpr (ForeignK
                  (ForeignSignature
                    ForeignLangC
                    cTemplate
                    argTypes
                    retType)
                  vals id expr) = do
        valsCode <- mapM compileV vals
        exprCode <- compileExpr expr
        return (fheader valsCode ++
                c_i_assign retType id
                  (cApply cTemplate
                    (zipWith3 i_c argTypes [1..] valsCode)) ++
               ";\n" ++
               ffooter ++
               exprCode)
      where
        fheader :: [CCode] -> CCode
        fheader valsCode
          | any i_c_requiresAlloc argTypes =
              "    {\n" ++
              concat (zipWith3 i_c_alloc argTypes [1..] valsCode)
              -- brace is closed in ffooter
          | otherwise = ""

        ffooter :: CCode
        ffooter
          -- brace is opened in fheader
          | any i_c_requiresAlloc argTypes =
              concat (zipWith i_c_free argTypes [1..]) ++
              "    }\n"
          | otherwise = ""

        -- Internal representation to C
        i_c :: ForeignType -> Integer -> CCode -> CCode
        i_c ForeignFixnum   _ v = "Qr_OBJ_AS_FIXNUM(" ++ v ++ ")"
        i_c ForeignChar     _ v = "Qr_OBJ_AS_FIXNUM(" ++ v ++ ")"
        i_c ForeignString   i _ = "_a" ++ show i
        i_c (ForeignPtr "") _ v = "Qr_OBJ_AS_PTR(" ++ v ++ ")"
        i_c (ForeignPtr t)  _ v = "((" ++ t ++ ")Qr_OBJ_AS_PTR(" ++ v ++ "))"
        i_c ForeignUnit     _ v = "0"
        i_c ForeignBool     _ v = "((" ++ v ++ ") == 1)"

        -- C to internal representation
        c_i_assign :: ForeignType -> IdK -> CCode -> CCode
        c_i_assign fType id v
          | c_i_requiresAlloc fType = c_i_alloc fType id v
          | otherwise = "    " ++ mangleVar id ++ " = " ++ c_i fType v ++ ";"

        c_i_requiresAlloc :: ForeignType -> Bool
        c_i_requiresAlloc ForeignString = True
        c_i_requiresAlloc _             = False

        c_i :: ForeignType -> CCode -> CCode
        c_i ForeignFixnum  v = "Qr_FIXNUM_AS_OBJ(" ++ v ++ ")"
        c_i ForeignChar    v = "Qr_FIXNUM_AS_OBJ(" ++ v ++ ")"
        c_i ForeignString  v = error ""
        c_i (ForeignPtr _) v = "((QrObj)Qr_PTR_AS_OBJ(" ++ v ++ "))"
        c_i ForeignUnit    v = "((" ++ v ++ "), 1)"
        c_i ForeignBool    v = "((" ++ v ++ ") ? 1 : 3)"

        c_i_alloc :: ForeignType -> IdK -> CCode -> CCode
        c_i_alloc ForeignString id str =
          "    {\n" ++
          "        QrObj _r = 1;\n" ++
          "        char *_s = " ++ str ++ ";\n" ++
          "        unsigned int _n = strlen(_s);\n" ++
          "        while (_n > 0) {\n" ++
          "            QrObj *rec;\n" ++
          "            Qr_MM_ALLOC(rec, 3)\n" ++
          "            rec[0] = Qr_RECORD_TAG(3);\n" ++
          "            rec[1] = Qr_FIXNUM_AS_OBJ(_s[--_n]);\n" ++
          "            rec[2] = _r;\n" ++
          "            _r = Qr_RECORD_AS_OBJ(rec);\n" ++
          "        }\n" ++
          "        " ++ mangleVar id ++ " = _r;\n" ++
          "    }\n"
        c_i_alloc _ _ _ = error ""

        -- Does the type require dynamic memory allocation?
        i_c_requiresAlloc :: ForeignType -> Bool
        i_c_requiresAlloc ForeignString = True
        i_c_requiresAlloc _             = False

        -- Allocate dynamically created objects
        i_c_alloc :: ForeignType -> Integer -> CCode -> CCode
        i_c_alloc ForeignString i v =
          "    char *_a" ++ show i ++ ";\n" ++ 
          "    {\n" ++
          "        QrObj _p = " ++ v ++ ";\n" ++
          "        unsigned int _n = 0;\n" ++
          "        while (Qr_OBJ_BOXED(_p)) {\n" ++
          "            _p = Qr_OBJ_AS_RECORD(_p)[2];\n" ++
          "            _n++;\n" ++
          "        }\n" ++
          "        _a" ++ show i ++ " = malloc(_n + 1);\n" ++
          "        _n = 0;\n" ++
          "        _p = " ++ v ++ ";\n" ++
          "        while (Qr_OBJ_BOXED(_p)) {\n" ++
          "            _a" ++ show i ++ "[_n] = " ++
          "Qr_OBJ_AS_FIXNUM(Qr_OBJ_AS_RECORD(_p)[1]);\n" ++
          "            _p = Qr_OBJ_AS_RECORD(_p)[2];\n" ++
          "            _n++;\n" ++
          "        }\n" ++
          "        _a" ++ show i ++ "[_n] = '\\0';\n" ++
          "    }\n"
        i_c_alloc _ _ _ = ""

        -- Free dynamically created objects
        i_c_free :: ForeignType -> Integer -> CCode
        i_c_free ForeignString i = "    free(_a" ++ show i ++ ");\n"
        i_c_free _ _ = ""

        cApply :: CCode -> [CCode] -> CCode
        cApply []             args = []
        cApply fmt@('$' : '{' : xs) args =
          let (iStr, xs') = span (/= '}') xs in
            case xs' of
              ('}' : xs'') ->
                case reads iStr of
                  [(i, _)] ->
                     if 1 <= i && i <= length args
                      then (args !! (i - 1)) ++ cApply xs'' args
                      else failApply
                  _ -> failApply
              xs'' -> failApply
          where
            failApply =
              error (
                 "(compileToC: formato gringo inválido:" ++
                    fmt ++
                  ")"
              )
        cApply (x : xs)   args = x : cApply xs args

    compileExpr (ForeignK (ForeignSignature lang _ _ _) _ _ _) = do
      error ("compileToC: lenguaje gringo no soportado: " ++ show lang ++ ")")

    callsSelf :: IdK -> ExprK -> Bool
    callsSelf x (RecordK _ _ expr) =
      callsSelf x expr
    callsSelf x (SelectK _ _ _ expr) =
      callsSelf x expr
    callsSelf x (AppK (LabelK y) _) = x == y
    callsSelf x (AppK _ _)          = False
    callsSelf x (LetK _ _) =
      error "(no debería encontrar un LetK)"
    callsSelf x (SwitchK _ exprs) =
      any (callsSelf x) exprs
    callsSelf x (PrimitiveK _ _ _ exprs) =
      any (callsSelf x) exprs
    callsSelf x (ForeignK _ _ _ expr) =
      callsSelf x expr

    assignUnit :: [IdK] -> CCode
    assignUnit []    = ""
    assignUnit [var] = "    " ++ mangleVar var ++ " = 0;\n"

    indent :: CCode -> CCode
    indent code = unlines (map ("    " ++) (lines code))
 
    compileV :: ValueK -> CM CCode
    compileV (LabelK label) =
      return $ "Qr_CONT_AS_OBJ(" ++ mangleLabel label ++ ")"
    compileV (VarK x) =
      return $ mangleVar x
    compileV (ConstantK (FixnumC n)) =
      return $ "(QrObj)(" ++ show (2 * n + 1) ++ ")"
    compileV (ConstantK (CharC c)) =
      compileV (ConstantK (FixnumC (fromIntegral (ord c))))
    compileV (SelK i x) =
      return $ "Qr_OBJ_AS_RECORD(" ++ mangleVar x ++ ")[" ++ show (i + 1) ++ "]"

    getFunctionFormals :: ValueK -> Integer -> CM [IdK]
    getFunctionFormals (LabelK f) n = do
      state <- get
      case Map.lookup f (cstFunctionFormals state) of
        Nothing     -> error ("(compileToC: la etiqueta no está definida)")
        Just params -> return params
    getFunctionFormals _ n = return [0..n - 1]

