
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

module AST(
        Id,
        PackageName,
        QualifId(..),
        Constant(..),
        TypeClass,
        MetavarId,
        PlaceholderId,
        ForeignLang(..),
        Pragma(..),
        AnnotTypeScheme(..),
        AnnotTypeConstraint(..),
        AnnotConstrainedType(..),
        AnnotConstructorDeclaration(..),
        AnnotMethodDeclaration(..),
        AnnotFieldDeclaration(..),
        AnnotMethodImplementation(..),
        AnnotType(..),
        AnnotPattern(..),
        AnnotMatchBranch(..),
        AnnotDeclaration(..),
        AnnotExpr(..),
        unfoldPlaceholders,
        showPackage,
        showBareId,
    ) where

import Data.Map as Map(Map, lookup)

type Id = String

type PackageName = [String]

showPackage :: PackageName -> String
showPackage [] = "[]"
showPackage p  = joinS "." p

joinS :: String -> [String] -> String
joinS sep []   = ""
joinS sep list = foldr1 (\ x r -> x ++ sep ++ r) list

data QualifId = QualifId PackageName Id
  deriving (Eq, Ord)

instance Show QualifId where
  show (QualifId package id) = joinS "." (package ++ [id])

showBareId :: QualifId -> String
showBareId (QualifId _ id) = id

data Constant = FixnumC Integer
              | CharC Char
  deriving (Show, Eq, Ord)

type TypeClass = QualifId

data AnnotTypeScheme a = ForallT [MetavarId] (AnnotConstrainedType a)
  deriving Show

data ForeignLang = ForeignLangC
                 | ForeignLangPy
                 | ForeignLangJvm
  deriving (Show, Eq, Ord)

data Pragma = ForeignPragma ForeignLang String
  deriving Show

data AnnotTypeConstraint a = TypeConstraint TypeClass (AnnotType a)
  deriving Eq

instance Show (AnnotTypeConstraint a) where
  show (TypeConstraint cls typ) = showBareId cls ++ " para " ++ show typ

data AnnotConstrainedType a =
     ConstrainedType [AnnotTypeConstraint a] (AnnotType a)
  deriving Eq

instance Show (AnnotConstrainedType a) where
  show (ConstrainedType [] typ) = show typ
  show (ConstrainedType [constraint] typ) =
    show typ ++ " con " ++ show constraint
  show (ConstrainedType constraints typ) =
    show typ ++ " con (" ++ joinS ", " (map show constraints) ++ ")"

data AnnotConstructorDeclaration a =
     ConstructorDeclaration QualifId [AnnotType a]
  deriving (Show, Eq)

data AnnotFieldDeclaration a =
     FieldDeclaration QualifId (AnnotType a)
  deriving (Show, Eq)

data AnnotMethodDeclaration a =
     MethodDeclaration QualifId (AnnotConstrainedType a)
  deriving (Show, Eq)

data AnnotMethodImplementation a =
     MethodImplementation QualifId (AnnotExpr a)
  deriving (Show, Eq)

data AnnotDeclaration a =
      AValueD    a QualifId (Maybe (AnnotConstrainedType a)) (AnnotExpr a)
    | ATypeD     a QualifId [QualifId] (AnnotType a)
    | ADatatypeD a QualifId                        -- type
                   [QualifId]                      -- parameters
                   [AnnotConstructorDeclaration a] -- constructors
    | AClassD    a TypeClass                       -- class
                   QualifId                        -- formal parameter
                   [AnnotMethodDeclaration a]      -- signature
    | AInstanceD a TypeClass                       -- class
                   (AnnotConstrainedType a)        -- argument
                   [AnnotMethodImplementation a]   -- implementation
    | AForeignD a ForeignLang                      -- foreign language
                  String                           -- foreign name
                  QualifId                         -- internal name
                  (AnnotType a)                    -- type
  deriving (Show, Eq)

data AnnotMatchBranch a = MatchBranch (AnnotPattern a) (AnnotExpr a)
  deriving (Show, Eq)

type PlaceholderId = Integer

data AnnotExpr a = AVarE         a QualifId
                 | AConstructorE a QualifId
                 | AConstantE    a Constant
                 | ALamE         a QualifId (AnnotExpr a)
                 | AAppE         a (AnnotExpr a) (AnnotExpr a)
                 | ALetE         a [AnnotDeclaration a] (AnnotExpr a)
                 | AMatchE       a (AnnotExpr a) [AnnotMatchBranch a]
                 | ATupleE       a [AnnotExpr a]
                 | APlaceholderE a PlaceholderId
    deriving (Show, Eq)

data AnnotPattern a = AVarP         a QualifId
                    | AConstructorP a QualifId [AnnotPattern a]
                    | AConstantP    a Constant
                    | AAnyP         a
                    | ATupleP       a [AnnotPattern a]
  deriving (Show, Eq)

type MetavarId = Integer

data AnnotType a = AVarT         a QualifId
                 | AConstructorT a QualifId
                 | AAppT         a (AnnotType a) (AnnotType a)
                 | AMetavarT     a MetavarId -- for type inference
  deriving Eq

instance Show (AnnotType a) where
  show (AVarT _ (QualifId _ id))         = id
  show (AConstructorT _ (QualifId ["PRIM"] "Tupla0")) = "()"
  show (AConstructorT _ (QualifId _ id)) = id
  show t@(AAppT _ _ _)
    | isFunction th ta =
      let [a1, a2] = ta in
        pShow a1 ++ " en " ++ show a2
    | isTuple th ta && length ta == 1 =
      show (head ta)
    | isTuple th ta =
      "(" ++ joinS ", " (map show ta) ++ ")"
    | isList th ta =
      let [a] = ta in
        "[" ++ show a ++ "]"
    | otherwise =
      show (tHead t) ++ " de " ++ joinS " " (map pShow (tArgs t))
    where
      th = tHead t
      ta = tArgs t
      tHead (AAppT _ t _)   = tHead t
      tHead t               = t
      tArgs (AAppT _ t1 t2) = tArgs t1 ++ [t2]
      tArgs t               = []

      pShow t@(AAppT _ _ _)
        | isTuple (tHead t) (tArgs t) = show t
        | isList (tHead t) (tArgs t)  = show t
        | otherwise                   = "(" ++ show t ++ ")"
      pShow t               = show t

      isFunction (AConstructorT _ (QualifId ["PRIM"] "Función")) [_, _] = True
      isFunction _ _ = False

      isTuple (AConstructorT _ (QualifId ["PRIM"] con)) args =
        con == "Tupla" ++ show (length args)
      isTuple _ _ = False

      isList (AConstructorT _ (QualifId ["PRIM"] "Lista")) [_] = True
      isList _ _ = False
    
  show (AMetavarT _ m) =
      metavars !! fromIntegral (m `mod` fromIntegral (length metavars)) ++
      suffix (m `div` fromIntegral (length metavars))
    where
      metavars :: [String]
      metavars = [
        "coso", "cosito", "fulano", "mengano", "zutano", "perengano",
        "fernández", "rodríguez", "gonzález", "garcía",
        "lópez", "martínez", "pérez", "álvarez", "gómez",
        "minga", "montoto", "magoya", "mongo", "cadorna", "pepe", "pepito",
        "sarasa"
       ]
      suffix :: Integer -> String
      suffix 0 = ""
      suffix n = show n

---- Functor

instance Functor AnnotTypeScheme where
  fmap f (ForallT vs t) = ForallT vs (fmap f t)

instance Functor AnnotTypeConstraint where
  fmap f (TypeConstraint cls t) = TypeConstraint cls (fmap f t)

instance Functor AnnotConstrainedType where
  fmap f (ConstrainedType cs t) = ConstrainedType (map (fmap f) cs) (fmap f t)

instance Functor AnnotConstructorDeclaration where
  fmap f (ConstructorDeclaration ident ts) =
   ConstructorDeclaration ident (map (fmap f) ts)

instance Functor AnnotMethodDeclaration where
  fmap f (MethodDeclaration ident t) = MethodDeclaration ident (fmap f t)

instance Functor AnnotMethodImplementation where
  fmap f (MethodImplementation ident expr) =
   MethodImplementation ident (fmap f expr)

instance Functor AnnotDeclaration where
  fmap f (AValueD ann ident mType expr)   =
         AValueD    (f ann) ident (fmap (fmap f) mType) (fmap f expr)
  fmap f (ATypeD ann ident ids t)         =
         ATypeD     (f ann) ident ids (fmap f t)
  fmap f (ADatatypeD ann ident ids cons)  =
         ADatatypeD (f ann) ident ids (map (fmap f) cons)
  fmap f (AClassD ann cls ident meths)    =
         AClassD    (f ann) cls ident (map (fmap f) meths)
  fmap f (AInstanceD ann cls t meths)     =
         AInstanceD (f ann) cls (fmap f t) (map (fmap f) meths)
  fmap f (AForeignD ann fl fn ident typ)  =
         AForeignD (f ann) fl fn ident (fmap f typ)
  
instance Functor AnnotMatchBranch where
  fmap f (MatchBranch pat exp) = MatchBranch (fmap f pat) (fmap f exp)

instance Functor AnnotExpr where
  fmap f (AVarE         ann ident)        =
         AVarE         (f ann) ident
  fmap f (AConstructorE ann ident)        =
         AConstructorE (f ann) ident
  fmap f (AConstantE    ann const)        =
         AConstantE    (f ann) const
  fmap f (ALamE         ann ident exp)    =
         ALamE         (f ann) ident (fmap f exp)
  fmap f (AAppE         ann e1 e2)        =
         AAppE         (f ann) (fmap f e1) (fmap f e2)
  fmap f (ALetE         ann decls exp)    =
         ALetE         (f ann) (map (fmap f) decls) (fmap f exp)
  fmap f (AMatchE       ann exp branches) =
         AMatchE       (f ann) (fmap f exp) (map (fmap f) branches)
  fmap f (ATupleE       ann exps)         =
         ATupleE       (f ann) (map (fmap f) exps)
  fmap f (APlaceholderE ann p)            =
         APlaceholderE (f ann) p

instance Functor AnnotPattern where
  fmap f (AVarP         ann ident)        =
         AVarP         (f ann) ident
  fmap f (AConstructorP ann ident pats)   =
         AConstructorP (f ann) ident (map (fmap f) pats)
  fmap f (AConstantP    ann const)        =
         AConstantP    (f ann) const
  fmap f (AAnyP         ann)              =
         AAnyP         (f ann)
  fmap f (ATupleP       ann pats)         =
         ATupleP       (f ann) (map (fmap f) pats)

instance Functor AnnotType where
  fmap f (AVarT         ann ident)        =
         AVarT         (f ann) ident
  fmap f (AConstructorT ann ident)        =
         AConstructorT (f ann) ident
  fmap f (AAppT         ann t1 t2)        =
         AAppT         (f ann) (fmap f t1) (fmap f t2)
  fmap f (AMetavarT     ann v)            =
         AMetavarT     (f ann) v

---- Unfold placeholders

class Unfoldable f where
  unfoldPlaceholders :: Map PlaceholderId (AnnotExpr annotation) ->
                        f annotation -> f annotation

instance Unfoldable AnnotMethodImplementation where
  unfoldPlaceholders dict (MethodImplementation ident expr) =
    MethodImplementation ident (unfoldPlaceholders dict expr)

instance Unfoldable AnnotDeclaration where
  unfoldPlaceholders dict (AValueD ann ident mType expr)    =
         AValueD    ann ident mType
                    (unfoldPlaceholders dict expr)
  unfoldPlaceholders dict (ATypeD ann ident ids t)          =
         ATypeD     ann ident ids t
  unfoldPlaceholders dict (ADatatypeD ann ident ids cons)   =
         ADatatypeD ann ident ids cons
  unfoldPlaceholders dict (AClassD ann cls ident methDecls) =
         AClassD    ann cls ident methDecls
  unfoldPlaceholders dict (AInstanceD ann cls t methImpls)  =
         AInstanceD ann cls t (map (unfoldPlaceholders dict) methImpls)
  unfoldPlaceholders dict (AForeignD ann fl fn ident typ)   =
         AForeignD ann fl fn ident typ
  
instance Unfoldable AnnotMatchBranch where
  unfoldPlaceholders dict (MatchBranch pat exp) =
    MatchBranch pat
                (unfoldPlaceholders dict exp)

instance Unfoldable AnnotExpr where
  unfoldPlaceholders dict (AVarE         ann ident)        =
         AVarE         ann ident
  unfoldPlaceholders dict (AConstructorE ann ident)        =
         AConstructorE ann ident
  unfoldPlaceholders dict (AConstantE    ann const)        =
         AConstantE    ann const
  unfoldPlaceholders dict (ALamE         ann ident exp)    =
         ALamE         ann ident (unfoldPlaceholders dict exp)
  unfoldPlaceholders dict (AAppE         ann e1 e2)        =
         AAppE         ann (unfoldPlaceholders dict e1)
                           (unfoldPlaceholders dict e2)
  unfoldPlaceholders dict (ALetE         ann decls exp)    =
         ALetE         ann (map (unfoldPlaceholders dict) decls)
                           (unfoldPlaceholders dict exp)
  unfoldPlaceholders dict (AMatchE       ann exp branches) =
         AMatchE       ann (unfoldPlaceholders dict exp)
                           (map (unfoldPlaceholders dict) branches)
  unfoldPlaceholders dict (ATupleE       ann exps)         =
         ATupleE       ann (map (unfoldPlaceholders dict) exps)
  unfoldPlaceholders dict (APlaceholderE ann p)            =
         case Map.lookup p dict of
           Nothing  -> APlaceholderE ann p
           Just exp -> unfoldPlaceholders dict exp

