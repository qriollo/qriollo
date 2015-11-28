
module ExpressionE(
        Id, PackageName, QualifId(..), Constant(..), TypeClass,
        MetavarId,
        PlaceholderId,
        ForeignLang(..),
        Pragma(..),
        AnnotTypeScheme(..), TypeScheme,
        AnnotTypeConstraint(..), TypeConstraint,
        AnnotConstrainedType(..), ConstrainedType,
        AnnotConstructorDeclaration(..), ConstructorDeclaration,
        AnnotMethodDeclaration(..), MethodDeclaration,
        AnnotFieldDeclaration(..), FieldDeclaration,
        AnnotMethodImplementation(..), MethodImplementation,
        AnnotType(..), Type,
        AnnotPattern(..), Pattern,
        AnnotMatchBranch(..), MatchBranch,
        AnnotDeclaration(..), Declaration,
        AnnotExpr(..), Expr,
        Annotation(..),

        naValueD, naTypeD, naDatatypeD, naClassD, naInstanceD, naForeignD,
        naVarE, naConstructorE, naConstantE, naLamE, naAppE, naLetE,
        naMatchE, naTupleE, naPlaceholderE,
        naVarP, naConstructorP, naConstantP, naAnyP, naTupleP,
        naVarT, naConstructorT, naAppT, naMetavarT,

        paValueD, paTypeD, paDatatypeD, paClassD, paInstanceD, paForeignD,
        paVarE, paConstructorE, paConstantE, paLamE, paAppE, paLetE,
        paMatchE, paTupleE, paPlaceholderE,
        paVarP, paConstructorP, paConstantP, paAnyP, paTupleP,
        paVarT, paConstructorT, paAppT, paMetavarT,

        unfoldPlaceholders, showPackage, showBareId, eraseAnnotations,
        mangleQualifId, joinS, replaceVariableE,
    ) where

import Data.List(union)

import AST(
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
        AnnotFieldDeclaration(..),
        AnnotMethodDeclaration(..),
        AnnotMethodImplementation(..),
        AnnotType(..),
        AnnotPattern(..),
        AnnotMatchBranch(..),
        AnnotDeclaration(..),
        AnnotExpr(..),
        unfoldPlaceholders,
        showPackage,
        showBareId,
    )
import Position(Position(..))

data Annotation = NA
                | AnnotatePosition Position
  deriving (Show, Eq)

type TypeScheme = AnnotTypeScheme Annotation
type TypeConstraint = AnnotTypeConstraint Annotation
type ConstrainedType = AnnotConstrainedType Annotation
type ConstructorDeclaration = AnnotConstructorDeclaration Annotation
type MethodDeclaration = AnnotMethodDeclaration Annotation
type FieldDeclaration = AnnotFieldDeclaration Annotation
type MethodImplementation = AnnotMethodImplementation Annotation
type Type = AnnotType Annotation
type Pattern = AnnotPattern Annotation
type MatchBranch = AnnotMatchBranch Annotation
type Declaration = AnnotDeclaration Annotation
type Expr = AnnotExpr Annotation

-- Without annotations

naValueD       = AValueD       NA
naTypeD        = ATypeD        NA
naDatatypeD    = ADatatypeD    NA
naClassD       = AClassD       NA
naInstanceD    = AInstanceD    NA
naForeignD     = AForeignD     NA
naVarE         = AVarE         NA
naConstructorE = AConstructorE NA
naConstantE    = AConstantE    NA
naLamE         = ALamE         NA
naAppE         = AAppE         NA
naLetE         = ALetE         NA
naMatchE       = AMatchE       NA
naTupleE       = ATupleE       NA
naPlaceholderE = APlaceholderE NA
naVarP         = AVarP         NA
naConstructorP = AConstructorP NA
naConstantP    = AConstantP    NA
naAnyP         = AAnyP         NA
naTupleP       = ATupleP       NA
naVarT         = AVarT         NA
naConstructorT = AConstructorT NA
naAppT         = AAppT         NA
naMetavarT     = AMetavarT     NA

-- Annotated with positions

paValueD       = AValueD       . annotatePosition
paTypeD        = ATypeD        . annotatePosition
paDatatypeD    = ADatatypeD    . annotatePosition
paClassD       = AClassD       . annotatePosition
paInstanceD    = AInstanceD    . annotatePosition
paForeignD     = AForeignD     . annotatePosition
paVarE         = AVarE         . annotatePosition
paConstructorE = AConstructorE . annotatePosition
paConstantE    = AConstantE    . annotatePosition
paLamE         = ALamE         . annotatePosition
paAppE         = AAppE         . annotatePosition
paLetE         = ALetE         . annotatePosition
paMatchE       = AMatchE       . annotatePosition
paTupleE       = ATupleE       . annotatePosition
paPlaceholderE = APlaceholderE . annotatePosition
paVarP         = AVarP         . annotatePosition
paConstructorP = AConstructorP . annotatePosition
paConstantP    = AConstantP    . annotatePosition
paAnyP         = AAnyP         . annotatePosition
paTupleP       = ATupleP       . annotatePosition
paVarT         = AVarT         . annotatePosition
paConstructorT = AConstructorT . annotatePosition
paAppT         = AAppT         . annotatePosition
paMetavarT     = AMetavarT     . annotatePosition

annotatePosition :: Position -> Annotation
annotatePosition (Position _ "" 0 0) = NA
annotatePosition pos                 = AnnotatePosition pos

eraseAnnotations :: Functor f => f Annotation -> f Annotation
eraseAnnotations = fmap (const NA)

mangleQualifId :: QualifId -> String
mangleQualifId (QualifId ps ident) = joinS "." (ps ++ [ident])

joinS :: String -> [String] -> String
joinS sep []   = ""
joinS sep list = foldr1 (\ x r -> x ++ sep ++ r) list

-- Note:
--     r (the expression that takes the place of x) should be fresh.
replaceVariableE :: QualifId -> Expr -> Expr -> Expr
replaceVariableE x r (AVarE ann y)
  | x == y    = r
  | otherwise = AVarE ann y
replaceVariableE x r (AConstructorE ann c) = AConstructorE ann c
replaceVariableE x r (AConstantE    ann c) = AConstantE ann c
replaceVariableE x r (ALamE ann y e)
  | x == y    = ALamE ann y e
  | otherwise = ALamE ann y (replaceVariableE x r e)
replaceVariableE x r (AAppE         ann e1 e2) =
  AAppE ann (replaceVariableE x r e1)
            (replaceVariableE x r e2)
replaceVariableE x r (ALetE ann decls e) =
    if x `elem` declBoundVars decls
     then ALetE ann decls e
     else ALetE ann (map repDecl decls) (replaceVariableE x r e)
  where
    declBoundVars :: [Declaration] -> [QualifId]
    declBoundVars [] = []
    declBoundVars (AValueD _ y _ _ : decls) = [y] `union` declBoundVars decls
    declBoundVars (_ : decls)               = declBoundVars decls

    repDecl :: Declaration -> Declaration
    repDecl (AValueD ann y typ exp) =
      AValueD ann y typ (replaceVariableE x r exp)
    repDecl decl = decl
replaceVariableE x r (AMatchE ann exp branches) =
    AMatchE ann (replaceVariableE x r exp)
                (map repBranch branches)
  where
    repBranch :: MatchBranch -> MatchBranch
    repBranch (MatchBranch pat exp) =
      if x `elem` patVars pat
       then MatchBranch pat exp
       else MatchBranch pat (replaceVariableE x r exp)
    patVars :: Pattern -> [QualifId]
    patVars (AVarP _ x)              = [x]
    patVars (AConstructorP _ _ pats) = foldr union [] (map patVars pats)
    patVars (AConstantP _ _)         = []
    patVars (AAnyP _)                = []
    patVars (ATupleP _ pats)         = foldr union [] (map patVars pats)
replaceVariableE x r (ATupleE ann es) =
  ATupleE ann (map (replaceVariableE x r) es)
replaceVariableE x r (APlaceholderE ann p) =
  error "Should not meet a placeholder"

