
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

module ExpressionK(
        IdK, ValueK(..), DeclarationK(..), ExprK(..), retK,
        allIds,
    ) where

import Data.Char(ord)

import ExpressionE
import ExpressionL

type IdK = Integer

data ValueK =
    VarK      IdK
  | ConstantK Constant
  | LabelK    IdK          -- Present only after the closure
                           -- conversion phase.
  | SelK      Integer IdK  -- Present only after the register
                           -- allocation phase.
                           -- Represents an indirection
                           -- into a record (and, in particular,
                           -- a spilled record).
  deriving (Show, Eq, Ord)

data DeclarationK = ValueDK IdK [IdK] ExprK
  deriving (Show, Eq, Ord)

data ExprK = RecordK    [ValueK] IdK ExprK
           | SelectK    Integer ValueK IdK ExprK
           | AppK       ValueK [ValueK]
           | LetK       [DeclarationK] ExprK
           | SwitchK    ValueK [ExprK]
           | PrimitiveK Primop [ValueK] [IdK] [ExprK]
           | ForeignK   ForeignSignature [ValueK] IdK ExprK
  deriving (Eq, Ord)

instance Show ExprK where
  show = exprKToCcp

retK :: ValueK -> ExprK
retK v = AppK (VarK (-1)) [v]

-- All identifiers in an expression

allIds :: ExprK -> [IdK]
allIds (RecordK vals id expr) =
  concatMap allIdsV vals ++ [id] ++ allIds expr
allIds (SelectK _ val id expr) = allIdsV val ++ [id] ++ allIds expr
allIds (AppK val vals) = allIdsV val ++ concatMap allIdsV vals
allIds (LetK decls expr) = concatMap allIdsD decls ++ allIds expr
  where
    allIdsD :: DeclarationK -> [IdK]
    allIdsD (ValueDK f args expr) = f : args ++ allIds expr
allIds (SwitchK val exprs) = allIdsV val ++ concatMap allIds exprs
allIds (PrimitiveK _ vals ids exprs) =
  concatMap allIdsV vals ++ ids ++ concatMap allIds exprs
allIds (ForeignK _ vals id expr) =
  concatMap allIdsV vals ++ [id] ++ allIds expr

allIdsV :: ValueK -> [IdK]
allIdsV (VarK id)   = [id]
allIdsV (LabelK id) = [id]
allIdsV (SelK _ id) = [id]
allIdsV _           = []

-- Show expression as a "C con Plica" program
exprKToCcp :: ExprK -> String
exprKToCcp expr = convert expr
  where
    convert :: ExprK -> String
    convert (RecordK vals id expr) =
      convId id ++ " := [" ++ joinS ", " (map convV vals) ++ "];\n" ++
      convert expr
    convert (SelectK n val id expr) =
      convId id ++ " := " ++ convV val ++ "[" ++ show n ++ "];\n" ++
      convert expr
    convert (AppK val vals) =
      convV val ++ "(" ++ joinS ", " (map convV vals) ++ ");\n"
    convert (LetK decls expr) =
      joinS "\n" (map convDecl decls) ++ "\n" ++
      "Main() {\n" ++
      indent (convert expr) ++
      "}\n"
    convert (SwitchK val exprs) =
      "switch " ++ convV val ++ " {\n" ++
      joinS "\n" (zipWith convertBranch [0..] exprs) ++
      "}\n"
    convert (PrimitiveK p vals [] [expr]) =
      show p ++ "(" ++ joinS ", " (map convV vals) ++ ");\n" ++
      convert expr
    convert (PrimitiveK p vals [id] [expr]) =
      convId id ++ " := " ++ show p ++
      "(" ++ joinS ", " (map convV vals) ++ ");\n" ++
      convert expr
    convert (PrimitiveK p vals [] [expr1, expr2]) =
      show p ++ "(" ++ joinS ", " (map convV vals) ++ ") {\n" ++
      indent (convert expr1) ++
      "} {\n" ++
      indent (convert expr2) ++
      "}\n"
    convert (ForeignK sig vals id expr) =
      convId id ++ " := foreign {" ++ show sig ++ "}" ++
      "(" ++ joinS ", " (map convV vals) ++ ");\n" ++
      convert expr

    indent :: String -> String
    indent xs = joinS "\n" (map ("  " ++) (lines xs)) ++ "\n"

    convertBranch :: Integer -> ExprK -> String
    convertBranch n expr =
      show n ++ ":\n" ++ indent (convert expr)

    convDecl :: DeclarationK -> String
    convDecl (ValueDK x xs body) =
      convLabel x ++ "(" ++ joinS ", " (map convId xs) ++ ") {\n" ++
      indent (convert body) ++
      "}\n"

    convId :: IdK -> String
    convId x = "r" ++ show x

    convLabel :: IdK -> String
    convLabel (-1) = "Return"
    convLabel x    = "L" ++ show x

    convV :: ValueK -> String
    convV (VarK x)                = convId x
    convV (ConstantK (FixnumC n)) = show n
    convV (ConstantK (CharC c))   = show (ord c)
    convV (LabelK x)              = convLabel x
    convV (SelK i x)              = convId x ++ "[" ++ show i ++ "]"

    joinS :: String -> [String] -> String
    joinS sep []   = ""
    joinS sep list = foldr1 (\ x r -> x ++ sep ++ r) list

