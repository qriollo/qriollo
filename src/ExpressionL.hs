
module ExpressionL(
        IdL, ConstructorRepresentation(..), Constructor(..),
        ForeignSignature(..), ForeignType(..), Primop(..),
        MatchLSpan(..), DeclarationL(..), MatchBranchL(..), ExprL(..),
        PrimopArity(..), primopArity
    ) where

import ExpressionE

type IdL = Integer

-- A constuctor applied to arguments is represented in one of
-- various ways. The representation for a constructor is chosen
-- during the precompilation phase.
--
-- (1) TaggedCR : A record whose first component is a fixnum constant
--                representing its tag.
--                RecordL [ConstantL (FixnumC <tag>), <arg1>, ..., <argN>]
--
-- (2) ConstantCR : An immediate fixnum constant.
--                  ConstantL (FixnumC <tag>)
--                  Only valid for constructors without arguments.
--
-- (3) UntaggedCR : A record without tag.
--                  RecordL [<arg1>, ..., <argN>]
--                  Only valid for a constructor which is the
--                  unique constructor of its type.
--
-- (4) SafeUntaggedCR : A safe variant of UntaggedCR
--                      which allows the record to coexist
--                      with other constructors, as long
--                      as they are all represented as immediate
--                      constants (ConstantCR).
--                      This forces the pattern match compiler
--                      to emit code to check for boxity.
--
-- (5) TransparentCR : No extra tags or records.
--                     Only valid for a constructor which is
--                     the unique constructor of its type and,
--                     moreover, has exactly one argument.
--
-- (6) RefCR : References are pseudo-constructors;
--             they are not represented by records but
--             constructing and deconstructing references
--             is rather translated to primitive calls.
--
data ConstructorRepresentation =
              TaggedCR Integer
            | ConstantCR Integer
            | SafeUntaggedCR
            | UntaggedCR
            | TransparentCR
            | RefCR
  deriving (Show, Eq)

data Constructor = DataConstructor ConstructorRepresentation
                 | ConstantConstructor Constant
  deriving (Show, Eq)

data Primop =
            -- Essential primitives for compiling the core language
            -- (arithmetic operations are required for pattern matching)
              PrimRef
            | PrimDeref
            | PrimAssign
            | PrimFixnumAdd
            | PrimFixnumSub
            | PrimFixnumEq
            | PrimFixnumLe
            | PrimBoxed -- Branch according to the boxity of a value.
                        -- If it is a record:
                        --   jump to the first branch.
                        -- If it is an immediate value:
                        --   jump to the second branch.
            | PrimTag   -- Returns the tag for a value.
                        -- If it is an immediate value:
                        --   return the value itself.
                        -- If it is a record:
                        --   return the value of its first field
                        --   which should always be immediate.

            -- Additional primitives
            | PrimPutChar

            | PrimReferenceEq
            | PrimFixnumMul
            | PrimFixnumDiv
            | PrimFixnumMod
            | PrimFixnumNe
            | PrimFixnumLt
            | PrimFixnumGe
            | PrimFixnumGt
            | PrimFixnumLshift
            | PrimFixnumRshift
            | PrimFixnumOrb
            | PrimFixnumAndb
            | PrimFixnumXorb
            | PrimFixnumNotb
            | PrimCharOrd
            | PrimCharChr
            | PrimSystemExit
            | PrimContinuationCallCC
            | PrimContinuationThrow
  deriving (Show, Eq, Ord)

data DeclarationL = ValueDL IdL ExprL
  deriving (Show, Eq)

data MatchBranchL = MatchBranchL Constructor ExprL
  deriving (Show, Eq)

data ForeignType = ForeignFixnum
                 | ForeignChar
                 | ForeignFloat
                 | ForeignString
                 | ForeignPtr String
                 | ForeignUnit
                 | ForeignBool
                 | ForeignMaybe ForeignType
                 | ForeignList ForeignType
                 -- For reifying exceptions,
                 -- should be used only as a return type
                 -- and should be nested at most once
                 | ForeignError ForeignType
  deriving (Show, Eq, Ord)

data ForeignSignature = ForeignSignature
                          ForeignLang 
                          String
                          [ForeignType]
                          ForeignType
  deriving (Show, Eq, Ord)

data MatchLSpan =
     MatchLSpansConstants
   | MatchLSpansConstructors [ConstructorRepresentation]
  deriving (Show, Eq)

data ExprL = VarL       IdL
           | ConstantL  Constant
           | LamL       IdL ExprL
           | AppL       ExprL ExprL
           | LetL       [DeclarationL] ExprL
           | MatchL     MatchLSpan ExprL [MatchBranchL] (Maybe ExprL)
           | RecordL    [ExprL]
           | SelectL    Integer ExprL
           | PrimitiveL Primop [ExprL]
           | ForeignL   ForeignSignature [ExprL]
  deriving (Show, Eq)

data PrimopArity = PrimopArity {
                     paArgs     :: Integer,
                     paBranches :: Integer
                   }
primopArity :: Primop -> PrimopArity
primopArity PrimRef       = PrimopArity 1 1
primopArity PrimDeref     = PrimopArity 1 1
primopArity PrimAssign    = PrimopArity 1 1
primopArity PrimFixnumAdd = PrimopArity 2 1
primopArity PrimFixnumSub = PrimopArity 2 1
primopArity PrimTag       = PrimopArity 1 1
primopArity PrimPutChar   = PrimopArity 1 1

-- Comparisons
primopArity PrimFixnumEq  = PrimopArity 2 2
primopArity PrimFixnumLe  = PrimopArity 2 2

--
primopArity PrimReferenceEq  = PrimopArity 2 2
primopArity PrimFixnumMul    = PrimopArity 2 1
primopArity PrimFixnumDiv    = PrimopArity 2 1
primopArity PrimFixnumMod    = PrimopArity 2 1
primopArity PrimFixnumNe     = PrimopArity 2 2
primopArity PrimFixnumLt     = PrimopArity 2 2
primopArity PrimFixnumGe     = PrimopArity 2 2
primopArity PrimFixnumGt     = PrimopArity 2 2
primopArity PrimFixnumLshift = PrimopArity 2 1
primopArity PrimFixnumRshift = PrimopArity 2 1
primopArity PrimFixnumOrb    = PrimopArity 2 1
primopArity PrimFixnumAndb   = PrimopArity 2 1
primopArity PrimFixnumXorb   = PrimopArity 2 1
primopArity PrimFixnumNotb   = PrimopArity 1 1
--
primopArity PrimCharOrd      = PrimopArity 1 1
primopArity PrimCharChr      = PrimopArity 1 1
primopArity PrimSystemExit   = PrimopArity 1 1

-- Continuations
primopArity PrimContinuationCallCC = PrimopArity 1 1
primopArity PrimContinuationThrow  = PrimopArity 2 1

