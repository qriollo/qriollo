
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

module Backend.Py(
        compileToPy,
        PyOptions(..), PyOptionsMangling(..), PyOptionsToplevel(..),
    ) where

import Data.Char(ord)
import Control.Monad(mapM_, zipWithM)
import Control.Monad.Trans.State.Lazy(State, get, put, modify, runState)
import qualified Data.Map as Map(
        Map, fromList, insert, lookup, keys, findWithDefault
    )
import Data.List(union, (\\), nub, sort)

import ExpressionE
import ExpressionL
import ExpressionK
import Primitive(primMaxFixnum)

unionMapM :: (Eq b, Monad m) => (a -> m [b]) -> [a] -> m [b]
unionMapM f xs = do
  xss <- mapM f xs
  return $ foldr union [] xss

data PyOptionsMangling = PyOpt_TrivialMangling
                       | PyOpt_MinimalMangling

data PyOptionsToplevel = PyOpt_ToplevelExit
                       | PyOpt_ToplevelShowAsString
  deriving (Read, Eq)

data PyOptions = PyOptions {
                   pyoMangling :: PyOptionsMangling,
                   pyoToplevel :: PyOptionsToplevel
                 }

data PyState = PyState {
                 pysIndent :: [Integer],
                 pysFunctionFormals :: Map.Map IdK [IdK],
                 pysFunctions :: [String],
                 pysNextLocalId :: Integer,
                 pysLocalDecls :: [(String, [(String, String)])],

                 -- For identifying self applications
                 pysCurrentFunction :: Maybe IdK,

                 -- Does the program use foreign functions, and
                 -- thus needs to convert between representations?
                 pysUseConversions :: Bool
               }

type PyM = State PyState

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

hex :: Integer -> String
hex = base 16

mangleInteger :: PyOptionsMangling -> Integer -> String
mangleInteger PyOpt_TrivialMangling n | n >= 0 = show n
mangleInteger PyOpt_MinimalMangling n | n >= 0 = base 62 n
mangleInteger _ n =
  error ("(mangleInteger: no se puede escribir " ++ show n ++ ")")

compileToPy :: PyOptions -> [Pragma] -> ExprK -> String
compileToPy options pragmas expr =
    let (string, state) = runState (pyExpr expr) initialState
     in "# coding:utf-8:\n" ++
        importsFor state ++
        string
  where
    initialState :: PyState
    initialState = PyState {
                     pysIndent = [0],
                     pysFunctionFormals = Map.fromList [
                       (-1, [0]) -- Toplevel continuation
                     ],
                     pysFunctions = [],
                     pysNextLocalId = 0,
                     pysLocalDecls = [],
                     pysCurrentFunction = Nothing,
                     pysUseConversions = False
                   }

    importsFor :: PyState -> String
    importsFor _ = concat . map importPackage $ importedPackages
      where
        importPackage :: String -> String
        importPackage package = "import " ++ package ++ "\n"

        importedPackages :: [String]
        importedPackages =
          nub ("sys" : concatMap pragmaPyImportedPackages pragmas)

        pragmaPyImportedPackages :: Pragma -> [String]
        pragmaPyImportedPackages (ForeignPragma ForeignLangPy declaration) =
          case words declaration of
            ["import", package] -> [package]
            _ -> []
        pragmaPyImports _ = []

    pyVar :: IdK -> PyM String
    pyVar x = return $ mangleVar x

    pyLabel :: IdK -> PyM String
    pyLabel x = return $ mangleLabel x

    pyAddLocalDecls :: (String, [(String, String)]) -> PyM ()
    pyAddLocalDecls localDecl =
      modify (\ state -> state {
        pysLocalDecls = localDecl : pysLocalDecls state
      })

    pyVal :: ValueK -> PyM String
    pyVal (VarK x)                = return $ mangleVar x
    pyVal (LabelK x)              = return $ mangleLabel x
    pyVal (ConstantK (FixnumC n)) = return $ show n
    pyVal (ConstantK (CharC c))   = return $ show (fromIntegral (ord c))
    pyVal (SelK i x)              =
      return $ mangleVar x ++ "[" ++ show i ++ "]"

    pyEscapeChar :: Char -> String
    pyEscapeChar '\'' = "\\\'"
    pyEscapeChar '\"' = "\\\""
    pyEscapeChar '\\' = "\\\\"
    pyEscapeChar c
      | printable c = [c]
      | ord c < 16   = "\\x0" ++ hex (fromIntegral (ord c))
      | ord c < 16^2 = "\\x"  ++ hex (fromIntegral (ord c))
      | ord c < 16^3 = "\\u0" ++ hex (fromIntegral (ord c))
      | otherwise    = "\\u"  ++ hex (fromIntegral (ord c))
      where
        printable :: Char -> Bool
        printable c = 32 <= ord c && ord c <= 127

    pyChar :: ValueK -> PyM String
    pyChar (VarK x)                = return $ "unichr(" ++ mangleVar x ++ ")"
    pyChar (LabelK x)              = return $ "unichr(" ++ mangleLabel x ++ ")"
    pyChar (ConstantK (FixnumC n)) = return $ "unichr(" ++ show n ++ ")"
    pyChar (ConstantK (CharC c))   = return $ "u'" ++ pyEscapeChar c ++ "'"

    pyString :: String -> PyM String
    pyString cs = return $ "u\"" ++ concatMap pyEscapeChar cs ++ "\""

    freshLocal :: PyM Integer
    freshLocal = do
      state <- get
      modify (\ state -> state {
        pysNextLocalId = pysNextLocalId state + 1
      })
      return $ pysNextLocalId state

    mangleVar :: Integer -> String
    mangleVar (-1) = error "no existe la variable -1"
    mangleVar n = "v_" ++ mangleInteger (pyoMangling options) n

    mangleLabel :: Integer -> String
    mangleLabel (-1) = "top"
    mangleLabel n    = "l_" ++ mangleInteger (pyoMangling options) n

    mangleLocal :: Integer -> String
    mangleLocal n = "c_" ++ mangleInteger (pyoMangling options) n

    mangleLocalArray :: Integer -> String
    mangleLocalArray n = "a_" ++ mangleInteger (pyoMangling options) n

    pushIndent :: PyM ()
    pushIndent =
      modify (\ state -> state {
        pysIndent = 0 : pysIndent state
      })

    popIndent :: PyM ()
    popIndent =
      modify (\ state -> state {
        pysIndent = tail (pysIndent state)
      })

    indent :: PyM ()
    indent =
      modify (\ state -> state {
        pysIndent = head (pysIndent state) + 1 : tail (pysIndent state)
      })

    tabs :: PyM String
    tabs = do
        state <- get
        return $ take (fromIntegral (tabWidth * head (pysIndent state)))
                      (repeat ' ')
      where
        tabWidth :: Integer
        tabWidth = 2

    unindent :: PyM ()
    unindent =
      modify (\ state -> state {
        pysIndent = head (pysIndent state) - 1 : tail (pysIndent state)
      })

    globalsFor :: [IdK] -> ExprK -> PyM [IdK]
    globalsFor params expr = do
      vs <- allVars expr
      return $ params `union` vs

    -- All variables in an expression

    allVars :: ExprK -> PyM [IdK]
    allVars (RecordK vals id expr) = do
      uVals <- unionMapM allVarsV vals
      uExpr <- allVars expr
      return (uVals `union` [id] `union` uExpr)
    allVars (SelectK _ val id expr) = do
      uVal  <- allVarsV val
      uExpr <- allVars expr
      return (uVal `union` [id] `union` uExpr)
    allVars (AppK val vals) = do
      formals <- pyFunctionFormals (fromIntegral (length vals)) val
      uVal  <- allVarsV val
      uVals <- unionMapM allVarsV vals
      return (formals `union` uVal `union` uVals)
    allVars (LetK decls expr) =
      error "(compileToPy/allVars: No debería encontrar un LetK)"
    allVars (SwitchK val _) = do
      -- Note: the expressions are compiled as separate functions
      allVarsV val
    allVars (PrimitiveK _ vals ids exprs) = do
      uVals  <- unionMapM allVarsV vals
      uExprs <- unionMapM allVars exprs
      return (uVals `union` ids `union` uExprs)
    allVars (ForeignK _ vals id expr) = do
      uVals <- unionMapM allVarsV vals
      uExpr <- allVars expr
      return (uVals `union` [id] `union` uExpr)

    allVarsV :: ValueK -> PyM [IdK]
    allVarsV (VarK id)   = return [id]
    allVarsV (SelK _ id) = return [id]
    allVarsV _           = return []

    hasSelfApplication :: IdK -> ExprK -> Bool
    hasSelfApplication x (RecordK _ _ expr) =
      hasSelfApplication x expr
    hasSelfApplication x (SelectK _ _ _ expr) =
      hasSelfApplication x expr
    hasSelfApplication x (AppK (LabelK y) _) = x == y
    hasSelfApplication x (AppK _ _)          = False
    hasSelfApplication x (LetK _ _) =
      error "(compileToPy/hasSelfApplication: no debería encontrar un LetK)"
    hasSelfApplication x (SwitchK _ exprs) = False -- Do not go inside switches
    hasSelfApplication x (PrimitiveK _ _ _ exprs) =
      any (hasSelfApplication x) exprs
    hasSelfApplication x (ForeignK _ _ _ expr) =
      hasSelfApplication x expr

    pyFunctionFormals :: Integer -> ValueK -> PyM [IdK]
    pyFunctionFormals _ (LabelK f) = do
      state <- get
      return $
        Map.findWithDefault
          (error "(pyFunctionFormals: la etiqueta no está definida.)")
          f
          (pysFunctionFormals state)
    pyFunctionFormals n _ = return [0..fromIntegral (n - 1)]

    pyGlobalDecl :: [IdK] -> ExprK -> PyM String
    pyGlobalDecl params expr = do
      t <- tabs
      globals  <- globalsFor params expr
      globals' <- mapM pyVar globals
      return (t ++ "global " ++ joinS ", " ("cont" : sort globals') ++ "\n")

    pyExpr :: ExprK -> PyM String
    pyExpr (RecordK vals x expr) = do
      vals' <- mapM pyVal vals
      x'    <- pyVar x
      expr' <- pyExpr expr
      t     <- tabs
      return (t ++ x' ++ " = " ++ tuple vals' ++ "\n" ++ expr')
    pyExpr (SelectK n val x expr) = do
      val'  <- pyVal val
      x'    <- pyVar x
      expr' <- pyExpr expr
      t     <- tabs
      return (t ++ x' ++ " = " ++ val' ++ "[" ++ show n ++ "]\n" ++ expr')
    pyExpr (AppK val vals) = do
        val' <- pyVal val
        t <- tabs
        formals    <- pyFunctionFormals (fromIntegral (length vals)) val
        assignment <- assignFormalsToVals formals vals

        state <- get
        let currentFunction = pysCurrentFunction state in do
          case (val, currentFunction) of
            (LabelK func, Just func')
              | func == func' ->
                 -- Self application is compiled as a `continue'
                 return (assignment ++
                         t ++ "continue\n")
            _ -> return (t ++ "cont = " ++ val' ++ "\n" ++
                        assignment ++
                        t ++ "return\n")
      where
        assignFormalsToVals :: [IdK] -> [ValueK] -> PyM String
        assignFormalsToVals formals vals =
          let formalsVals2 = filter (\ (f, v) -> v /= VarK f)
                                    (zip formals vals)
              formals2 = map fst formalsVals2
              vals2    = map snd formalsVals2
           in
            if null formalsVals2
             then return ""
             else do
               t <- tabs
               vals' <- mapM pyVal vals2
               formals' <- mapM pyVar formals2
               return (
                 t ++ joinS ", " formals' ++ " = " ++
                      joinS ", " vals' ++ "\n")

    pyExpr (LetK decls expr) = do
        mapM_ pyDeclare decls
        decls' <- mapM pyDecl decls
        indent
        globals <- pyGlobalDecl [] expr
        expr'  <- pyExpr expr
        unindent
        localArrays <- localArrayDefinitions
        t <- tabs
        defs <- complementaryDefinitions
        return (localArrays ++
                joinS "" decls' ++
                t ++ "def main():\n" ++
                globals ++
                expr' ++
                defs)
      where
        pyDeclare :: DeclarationK -> PyM ()
        pyDeclare (ValueDK x params _) =
          modify (\ state -> state {
            pysFunctionFormals =
              Map.insert x params (pysFunctionFormals state)
          })

        pyDecl :: DeclarationK -> PyM String
        pyDecl (ValueDK x params body) = do
          t <- tabs
          x' <- pyLabel x
          modify (\ state -> state {
            pysCurrentFunction = Just x
          })
          let selfApp = hasSelfApplication x body in do
            indent
            globals <- pyGlobalDecl params body
            if selfApp
             then indent
             else return ()
            body' <- pyExpr body
            unindent
            if selfApp
             then unindent
             else return ()
            modify (\ state -> state {
              pysCurrentFunction = Nothing
            })
            return (t ++ "def " ++ x' ++ "():\n" ++
                    globals ++
                    (if selfApp then "  while True:\n" else "") ++
                    body')

        localArrayDefinitions :: PyM String
        localArrayDefinitions = do
          state <- get
          return $
            joinS "\n"
                   (map (\ (array, funcs) ->
                          joinS "" (map snd funcs) ++
                          array ++ " = " ++ tuple (map fst funcs) ++ "\n")
                        (pysLocalDecls state))
    pyExpr (SwitchK val exprs) = do
        val'       <- pyVal val
        localArray <- freshLocal
        localIds   <- mapM (const freshLocal) exprs
        localDecls <- zipWithM localDecl localIds exprs
        pyAddLocalDecls (mangleLocalArray localArray, localDecls)
        t <- tabs
        return (
          t ++ "cont = " ++ mangleLocalArray localArray
            ++ "[" ++ val' ++ "]\n" ++
          t ++ "return\n")
      where
        localDecl :: Integer -> ExprK -> PyM (String, String)
        localDecl n body = do
          state <- get
          let oldCurrentFunction = pysCurrentFunction state in do
            modify (\ state -> state {
              pysCurrentFunction = Nothing
            })
            pushIndent
            indent
            globals <- pyGlobalDecl [] body           
            body' <- pyExpr body
            unindent
            popIndent
            modify (\ state -> state {
              pysCurrentFunction = oldCurrentFunction
            })
            let localName = mangleLocal n in do
              return (localName,
                      "def " ++ localName ++ "():\n" ++
                      globals ++
                      body')
    pyExpr (PrimitiveK PrimRef [val] [x] [expr]) = do
      t     <- tabs
      val'  <- pyVal val
      x'    <- pyVar x
      expr' <- pyExpr expr
      return (t ++ x' ++ " = [" ++ val' ++ "]\n" ++ expr')
    pyExpr (PrimitiveK PrimDeref [val] [x] [expr]) = do
      t     <- tabs
      val'  <- pyVal val
      x'    <- pyVar x
      expr' <- pyExpr expr
      return (t ++ x' ++ " = " ++ val' ++ "[0]\n" ++ expr')
    -- For value and effect
    pyExpr (PrimitiveK PrimAssign [vref, vval] [x] [expr]) = do
      t     <- tabs
      vref' <- pyVal vref
      vval' <- pyVal vval
      x'    <- pyVar x
      expr' <- pyExpr expr
      return (t ++ vref' ++ "[0] = " ++ vval' ++ "\n" ++
              t ++ x' ++ " = 0\n" ++
              expr')
    -- For effect
    pyExpr (PrimitiveK PrimAssign [vref, vval] [] [expr]) = do
      t     <- tabs
      vref' <- pyVal vref
      vval' <- pyVal vval
      expr' <- pyExpr expr
      return (t ++ vref' ++ "[0] = " ++ vval' ++ "\n" ++
              expr')
    pyExpr (PrimitiveK PrimFixnumAdd [val1, val2] [x] [expr]) = do
      t     <- tabs
      val1' <- pyVal val1
      val2' <- pyVal val2
      x'    <- pyVar x
      expr' <- pyExpr expr
      return (t ++ x' ++ " = (" ++ val1' ++ " + " ++ val2' ++ ")" ++
                         " & 0x" ++ hex primMaxFixnum ++
                         "\n" ++
                         expr')
    pyExpr (PrimitiveK PrimFixnumSub [val1, val2] [x] [expr]) = do
      t     <- tabs
      val1' <- pyVal val1
      val2' <- pyVal val2
      x'    <- pyVar x
      expr' <- pyExpr expr
      return (t ++ x' ++ " = (" ++ val1' ++ " - " ++ val2' ++ ")" ++
                         " & 0x" ++ hex primMaxFixnum ++
                         "\n" ++
                         expr')
    pyExpr (PrimitiveK PrimFixnumEq [val1, val2] [] [expr1, expr2]) = do
      t      <- tabs
      val1'  <- pyVal val1
      val2'  <- pyVal val2
      indent
      expr1' <- pyExpr expr1
      expr2' <- pyExpr expr2
      unindent
      return (t ++ "if " ++ val1' ++ " == " ++ val2' ++ ":\n" ++
                    expr1' ++
                    t ++ "else:\n" ++
                    expr2')
    pyExpr (PrimitiveK PrimFixnumLe [val1, val2] [] [expr1, expr2]) = do
      t      <- tabs
      val1'  <- pyVal val1
      val2'  <- pyVal val2
      indent
      expr1' <- pyExpr expr1
      expr2' <- pyExpr expr2
      unindent
      return (t ++ "if " ++ val1' ++ " <= " ++ val2' ++ ":\n" ++
                    expr1' ++
                    t ++ "else:\n" ++
                    expr2')

    pyExpr (PrimitiveK PrimFixnumMul [val1, val2] [x] [expr]) = do
      t     <- tabs
      val1' <- pyVal val1
      val2' <- pyVal val2
      x'    <- pyVar x
      expr' <- pyExpr expr
      return (t ++ x' ++ " = (" ++ val1' ++ " * " ++ val2' ++ ")" ++
                         " & 0x" ++ hex primMaxFixnum ++
                         "\n" ++
                         expr')

    pyExpr (PrimitiveK PrimFixnumDiv [val1, val2] [x] [expr]) = do
      t     <- tabs
      val1' <- pyVal val1
      val2' <- pyVal val2
      x'    <- pyVar x
      expr' <- pyExpr expr
      return (t ++ x' ++ " = (" ++ val1' ++ " // " ++ val2' ++ ")" ++
                         " & 0x" ++ hex primMaxFixnum ++
                         "\n" ++
                         expr')

    pyExpr (PrimitiveK PrimFixnumMod [val1, val2] [x] [expr]) = do
      t     <- tabs
      val1' <- pyVal val1
      val2' <- pyVal val2
      x'    <- pyVar x
      expr' <- pyExpr expr
      return (t ++ x' ++ " = (" ++ val1' ++ " % " ++ val2' ++ ")" ++
                         " & 0x" ++ hex primMaxFixnum ++
                         "\n" ++
                         expr')

    pyExpr (PrimitiveK PrimFixnumLt [val1, val2] [] [expr1, expr2]) = do
      t      <- tabs
      val1'  <- pyVal val1
      val2'  <- pyVal val2
      indent
      expr1' <- pyExpr expr1
      expr2' <- pyExpr expr2
      unindent
      return (t ++ "if " ++ val1' ++ " < " ++ val2' ++ ":\n" ++
                    expr1' ++
                    t ++ "else:\n" ++
                    expr2')

    pyExpr (PrimitiveK PrimFixnumNe [val1, val2] [] [expr1, expr2]) = do
      t      <- tabs
      val1'  <- pyVal val1
      val2'  <- pyVal val2
      indent
      expr1' <- pyExpr expr1
      expr2' <- pyExpr expr2
      unindent
      return (t ++ "if " ++ val1' ++ " != " ++ val2' ++ ":\n" ++
                    expr1' ++
                    t ++ "else:\n" ++
                    expr2')

    pyExpr (PrimitiveK PrimFixnumGt [val1, val2] [] [expr1, expr2]) = do
      t      <- tabs
      val1'  <- pyVal val1
      val2'  <- pyVal val2
      indent
      expr1' <- pyExpr expr1
      expr2' <- pyExpr expr2
      unindent
      return (t ++ "if " ++ val1' ++ " > " ++ val2' ++ ":\n" ++
                    expr1' ++
                    t ++ "else:\n" ++
                    expr2')

    pyExpr (PrimitiveK PrimFixnumGe [val1, val2] [] [expr1, expr2]) = do
      t      <- tabs
      val1'  <- pyVal val1
      val2'  <- pyVal val2
      indent
      expr1' <- pyExpr expr1
      expr2' <- pyExpr expr2
      unindent
      return (t ++ "if " ++ val1' ++ " >= " ++ val2' ++ ":\n" ++
                    expr1' ++
                    t ++ "else:\n" ++
                    expr2')

    pyExpr (PrimitiveK PrimFixnumLshift [val1, val2] [x] [expr]) = do
      t     <- tabs
      val1' <- pyVal val1
      val2' <- pyVal val2
      x'    <- pyVar x
      expr' <- pyExpr expr
      return (t ++ x' ++ " = (" ++ val1' ++ " << " ++ val2' ++ ")" ++
                         " & 0x" ++ hex primMaxFixnum ++
                         "\n" ++
                         expr')

    pyExpr (PrimitiveK PrimFixnumRshift [val1, val2] [x] [expr]) = do
      t     <- tabs
      val1' <- pyVal val1
      val2' <- pyVal val2
      x'    <- pyVar x
      expr' <- pyExpr expr
      return (t ++ x' ++ " = (" ++ val1' ++ " >> " ++ val2' ++ ")" ++
                         " & 0x" ++ hex primMaxFixnum ++
                         "\n" ++
                         expr')

    pyExpr (PrimitiveK PrimFixnumOrb [val1, val2] [x] [expr]) = do
      t     <- tabs
      val1' <- pyVal val1
      val2' <- pyVal val2
      x'    <- pyVar x
      expr' <- pyExpr expr
      return (t ++ x' ++ " = (" ++ val1' ++ " | " ++ val2' ++ ")" ++
                         " & 0x" ++ hex primMaxFixnum ++
                         "\n" ++
                         expr')

    pyExpr (PrimitiveK PrimFixnumAndb [val1, val2] [x] [expr]) = do
      t     <- tabs
      val1' <- pyVal val1
      val2' <- pyVal val2
      x'    <- pyVar x
      expr' <- pyExpr expr
      return (t ++ x' ++ " = (" ++ val1' ++ " & " ++ val2' ++ ")" ++
                         " & 0x" ++ hex primMaxFixnum ++
                         "\n" ++
                         expr')

    pyExpr (PrimitiveK PrimFixnumXorb [val1, val2] [x] [expr]) = do
      t     <- tabs
      val1' <- pyVal val1
      val2' <- pyVal val2
      x'    <- pyVar x
      expr' <- pyExpr expr
      return (t ++ x' ++ " = (" ++ val1' ++ " ^ " ++ val2' ++ ")" ++
                         " & 0x" ++ hex primMaxFixnum ++
                         "\n" ++
                         expr')

    pyExpr (PrimitiveK PrimFixnumNotb [val1] [x] [expr]) = do
      t     <- tabs
      val1' <- pyVal val1
      x'    <- pyVar x
      expr' <- pyExpr expr
      return (t ++ x' ++ " = (~" ++ val1' ++ ")" ++
                         " & 0x" ++ hex primMaxFixnum ++
                         "\n" ++
                         expr')

    pyExpr (PrimitiveK PrimCharOrd [val] [x] [expr]) = do
      t     <- tabs
      val'  <- pyVal val
      x'    <- pyVar x
      expr' <- pyExpr expr
      return (t ++ x' ++ " = " ++ val' ++ "\n" ++
                         expr')

    pyExpr (PrimitiveK PrimCharChr [val] [x] [expr]) = do
      t     <- tabs
      val'  <- pyVal val
      x'    <- pyVar x
      expr' <- pyExpr expr
      return (t ++ x' ++ " = " ++ val' ++ "\n" ++
                         expr')

    pyExpr (PrimitiveK PrimReferenceEq [val1, val2] [] [expr1, expr2]) = do
      t      <- tabs
      val1'  <- pyVal val1
      val2'  <- pyVal val2
      indent
      expr1' <- pyExpr expr1
      expr2' <- pyExpr expr2
      unindent
      return (t ++ "if id(" ++ val1' ++ ") == id(" ++ val2' ++ "):\n" ++
                    expr1' ++
                    t ++ "else:\n" ++
                    expr2')

    pyExpr (PrimitiveK PrimSystemExit [val] [x] [expr]) = do
      t     <- tabs
      val'  <- pyVal val
      expr' <- pyExpr expr
      return (t ++ "sys.exit(" ++ val' ++ ")\n" ++
                   expr')

    pyExpr (PrimitiveK PrimBoxed [val] [] [expr1, expr2]) = do
      t      <- tabs
      val'   <- pyVal val
      indent
      expr1' <- pyExpr expr1
      expr2' <- pyExpr expr2
      unindent
      return (t ++ "if isinstance(" ++ val' ++ ", tuple):\n" ++
                    expr1' ++
                    t ++ "else:\n" ++
                    expr2')
    pyExpr (PrimitiveK PrimTag [val] [x] [expr]) = do
      t     <- tabs
      val'  <- pyVal val
      x'    <- pyVar x
      expr' <- pyExpr expr
      return (t ++ "if isinstance(" ++ val' ++ ", tuple):\n" ++
              t ++ "  " ++ x' ++ " = " ++ val' ++ "[0]\n" ++
              t ++ "else:\n" ++
              t ++ "  " ++ x' ++ " = " ++ val' ++ "\n" ++
              expr')
    -- For value and effect
    pyExpr (PrimitiveK PrimPutChar [val] [x] [expr]) = do
      t     <- tabs
      val'  <- pyChar val
      x'    <- pyVar x
      expr' <- pyExpr expr
      return (t ++ "write(" ++ val' ++ ")\n" ++
              t ++ x' ++ " = 0\n" ++
              expr')
    -- For effect
    pyExpr expr@(PrimitiveK PrimPutChar [ConstantK (CharC _)] [] [_]) =
      pyPutString "" expr
    pyExpr (PrimitiveK PrimPutChar [val] [] [expr]) = do
      t     <- tabs
      val'  <- pyChar val
      expr' <- pyExpr expr
      return (t ++ "write(" ++ val' ++ ")\n" ++
              expr')
    pyExpr (PrimitiveK primop vals ids exprs) = do
      error ("(compileToPy: primitiva " ++ show primop ++ " no implementada)")
    pyExpr (ForeignK
              (ForeignSignature ForeignLangPy name argTypes retType)
              vals x expr) = do
      useConversions
      x' <- pyVar x
      vals' <- mapM pyVal vals
      let args = zipWith i_p argTypes vals' in do
        t <- tabs
        res <- assignResult x' retType (pyApply name args)
        expr' <- pyExpr expr
        return (res ++ expr')
      where
        -- Internal representation to Python
        i_p :: ForeignType -> String -> String
        i_p ForeignFixnum   v = v
        i_p ForeignChar     v = "unichr(" ++ v ++ ")"
        i_p ForeignFloat    v = v
        i_p ForeignString   v = "string_ip(" ++ v ++ ")"
        i_p (ForeignPtr _)  v = v
        i_p ForeignUnit     v = v
        i_p ForeignBool     v = "(" ++ v ++ " == 0)"

        -- Python to internal representation
        p_i :: ForeignType -> String -> String
        p_i ForeignFixnum  v = v
        p_i ForeignChar    v = "ord(" ++ v ++ ")"
        p_i ForeignFloat   v = v
        p_i ForeignString  v = "string_pi(" ++ v ++ ")"
        p_i (ForeignPtr _) v = v
        p_i ForeignUnit    v = v
        p_i ForeignBool    v = "(0 if " ++ v ++ " else 1)"

        -- Trap exceptions
        assignResult :: String -> ForeignType -> String -> PyM String
        assignResult x (ForeignError typ) v = do
          t <- tabs
          return (
            t ++ "try:\n" ++
            t ++ "  " ++ x ++ " = (1, " ++ p_i typ v ++ ")\n" ++
            t ++ "except Exception as e:\n" ++
            t ++ "  " ++ x ++ " = (0, string_pi(str(e)))\n")
        assignResult x typ v = do
          t <- tabs
          return (t ++ x ++ " = " ++ p_i typ v ++ "\n")

        pyApply :: String -> [String] -> String
        pyApply []             args = []
        pyApply fmt@('$' : '{' : xs) args =
          let (iStr, xs') = span (/= '}') xs in
            case xs' of
              ('}' : xs'') ->
                case reads iStr of
                  [(i, _)] ->
                     if 1 <= i && i <= length args
                      then (args !! (i - 1)) ++ pyApply xs'' args
                      else failApply
                  _ -> failApply
              xs'' -> failApply
          where
            failApply =
              error (
                 "(compileToPy: formato gringo inválido:" ++
                    fmt ++
                  ")"
              )
        pyApply (x : xs)   args = x : pyApply xs args
    pyExpr (ForeignK (ForeignSignature lang _ _ _) _ _ _) =
      error ("(compileToPy: lenguaje gringo no soportado: " ++
             show lang ++ ")")

    pyPutString :: String -> ExprK -> PyM String
    pyPutString s (PrimitiveK PrimPutChar [ConstantK (CharC chr)] [] [expr]) =
      pyPutString (s ++ [chr]) expr
    pyPutString s expr = do
      t     <- tabs
      s'    <- pyString s
      expr' <- pyExpr expr
      return (t ++ "write(" ++ s' ++ ")\n" ++
              expr')

    useConversions :: PyM ()
    useConversions = modify (\ state -> state {
        pysUseConversions = True
    })

    complementaryDefinitions :: PyM String
    complementaryDefinitions = do
        state <- get
        conversions' <-
          if pysUseConversions state
           then return conversions
           else return ""
        return (conversions' ++ driver)
      where
        driver :: String
        driver = "write = sys.stdout.write\n" ++
                 toplevel ++
                 "cont = main\n" ++
                 "while True:\n" ++
                 "  cont()\n"

        toplevel :: String
        toplevel
          | pyoToplevel options == PyOpt_ToplevelExit =
                 "def top():\n" ++
                 "  sys.exit(0)\n"
          | pyoToplevel options == PyOpt_ToplevelShowAsString =
                 "def top():\n" ++
                 "  global v_0\n" ++
                 "  while isinstance(v_0, tuple):\n" ++
                 "    write(unichr(v_0[0]))\n" ++
                 "    v_0 = v_0[1]\n" ++
                 "  sys.exit(0)\n"

        conversions :: String
        conversions =
          -- Internal representation to Python
          "def string_ip(x):\n" ++
          "  s = u\"\"\n" ++
          "  while isinstance(x, tuple):\n" ++
          "    s += unichr(x[0])\n" ++
          "    x = x[1]\n" ++
          "  return s\n" ++
          -- Python to internal representation
          "def string_pi(s):\n" ++
          "  r = 0\n" ++
          "  for i in range(len(s), 0, -1):\n" ++
          "    r = (ord(s[i - 1]), r)\n" ++
          "  return r\n" ++
          ""

    tuple :: [String] -> String
    tuple []  = "()"
    tuple [x] = "(" ++ x ++ ",)"
    tuple xs  = "(" ++ joinS ", " xs ++ ")"

