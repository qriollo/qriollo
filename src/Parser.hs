
module Parser(
        ParserOptions(..),
        Declaration(..),
        MethodDeclaration(..),
        MethodImplementation(..),
        parseFromString,
        parseFromStringOrFail,
        parsePackagesWithPragmas,
        parsePackages,
        parsePackagesOrFail,
    ) where

import ExpressionE
import Control.Monad.Trans.State.Lazy(
        State, StateT(..), get, modify, evalState, runStateT,
    )
import Data.Maybe(fromJust)
import Data.List(sortBy, groupBy, nub)
import Data.Function(on)
import qualified Data.Map as Map(
        Map, empty, insert, lookup, findWithDefault, keys, fromList
    )

import Primitive(
        primPackage, primFunction, primTFunction, primTTuple,
        primTList, primListNil, primListCons, primString,
        primExports, primBoolTrue, primMonadBind, primFromDigits,
        primMaxFixnum, primPtrPrefix, primPtr, primTPtr,
    )
import Position(Position(..), describePosition, showNearbyCode)
import Lexer(packageFor, Token(..), TokenType(..), tokenize, describeTokenType)

-- Operators finishing with colon (:) are constructors
operatorIsConstructor :: Id -> Bool
operatorIsConstructor id | last id == ':' = True
operatorIsConstructor _                   = False

operatorE :: QualifId -> Expr
operatorE qualifId@(QualifId _ opId)
  | not (null opId) && operatorIsConstructor opId = naConstructorE qualifId
  | otherwise                                     = naVarE qualifId

data Associativity = AssocLeft | AssocRight | AssocPrefix
  deriving (Show, Eq)
type Precedence = Integer
data Operator = Operator { operatorAssociativity :: Associativity,
                           operatorPrecedence :: Precedence,
                           operatorId :: QualifId }
  deriving Show

isBinaryOperator :: Operator -> Bool
isBinaryOperator (Operator AssocLeft _ _)  = True
isBinaryOperator (Operator AssocRight _ _) = True
isBinaryOperator _                         = False

isUnaryOperator :: Operator -> Bool
isUnaryOperator (Operator AssocPrefix _ _) = True
isUnaryOperator _                          = False

isLeftAssoc :: Operator -> Bool
isLeftAssoc (Operator AssocLeft _ _) = True
isLeftAssoc _                        = False

data PackageInfo = PackageInfo {
                     pInfoPackageNames :: PackageNames,
                     pInfoPackageExportedNames :: PackageExportedNames,
                     pInfoImportedPackages :: [PackageName]
                   }
type PackageNames = Map.Map Id QualifId
data PackageExportedNames = PackageExportAll | PackageExportNames [Id]

pInfoEmpty :: PackageInfo
pInfoEmpty = PackageInfo {
               pInfoPackageNames =
                Map.fromList $
                map (\ id -> (id, QualifId primPackage id))
                    primExports,
               pInfoPackageExportedNames = PackageExportAll,
               pInfoImportedPackages = [primPackage]
             }

---- Parser monad

data ParserState = ParserState {
                     psOptions :: ParserOptions,
                     psNextFreshId :: Integer,
                     psStream :: [Token],
                     psOperators :: [Operator],
                     psPackageStack :: [PackageName],
                     psPackageInfo :: Map.Map PackageName PackageInfo,
                     -- Records
                     psRecordFields :: Map.Map QualifId [QualifId],
                     psFields :: Map.Map QualifId (),
                     -- Pragmas
                     psPragmas :: [Pragma]
                   }
type ParserM a = StateT ParserState (Either String) a

type FeatureName = String

data ParserOptions =
     ParserOptions {
         parserOptionsFeatures :: [FeatureName]
     }


parserGetState :: ParserM ParserState
parserGetState = get

parserModifyState :: (ParserState -> ParserState) -> ParserM ()
parserModifyState = modify

-- parserFail should be defined using lift, which seems to have a bug
-- this is a workaround
parserFail :: String -> Position -> ParserM a
parserFail msg pos =
  StateT . const . Left $ (
     msg ++ "\n" ++
     "\nCerquita de: " ++ describePosition pos ++ ".\n" ++
     "----\n" ++ showNearbyCode pos ++ "\n----\n"
  )

runParserM :: ParserOptions -> [Token] -> ParserM a ->
              Either String ([Pragma], a)
runParserM parserOptions tokens parser =
    case runStateT parser initialState of
      Left msg              -> Left msg
      Right (result, state) -> Right (psPragmas state, result)
  where initialState = ParserState {
            psOptions = parserOptions,
            psNextFreshId = 0,
            psStream = tokens,
            psOperators = [],
            psPackageStack = [],
            psPackageInfo = Map.insert primPackage primPackageInfo Map.empty,
            psRecordFields = Map.empty,
            psFields = Map.empty,
            psPragmas = []
        }
        primPackageInfo =
          PackageInfo {
            pInfoPackageNames =
                Map.fromList $
                map (\ id -> (id, QualifId primPackage id))
                    primExports,
            pInfoPackageExportedNames = PackageExportNames [],
            pInfoImportedPackages = [primPackage]
          }

orFail :: Either String a -> a
orFail e = case e of
             Right x  -> x
             Left msg -> error msg

----

parserFreshQualifId :: ParserM QualifId
parserFreshQualifId = do
  s <- parserGetState
  parserModifyState (\ s -> s { psNextFreshId = psNextFreshId s + 1 })
  return $ QualifId primPackage
                    ("{parser|" ++ show (psNextFreshId s) ++ "}")

----

parserPushPackage :: PackageName -> ParserM ()
parserPushPackage package = do
  parserModifyState (\ s -> s {
    psPackageStack = package : psPackageStack s,
    psPackageInfo = Map.insert package pInfoEmpty (psPackageInfo s)
  })

parserPopPackage :: ParserM ()
parserPopPackage =
  parserModifyState (\ s -> s { psPackageStack = tail (psPackageStack s) })

parserGetCurrentPosition :: ParserM Position
parserGetCurrentPosition = do
  Token _ pos <- parserPeek
  return pos

parserGetCurrentPackage :: ParserM PackageName
parserGetCurrentPackage = do
  s <- parserGetState
  if null (psPackageStack s)
   then error "(parserGetCurrentPackage: pila de paquetes vacía)"
   else return $ head (psPackageStack s)

---- Packages

parserGetPackageInfo :: PackageName -> ParserM PackageInfo
parserGetPackageInfo package = do
  s <- parserGetState
  return $ Map.findWithDefault pInfoEmpty package (psPackageInfo s)

parserModifyPackageInfo :: PackageName -> (PackageInfo -> PackageInfo) ->
                           ParserM ()
parserModifyPackageInfo package f =
    parserModifyState (\ s -> s {
      psPackageInfo = update (psPackageInfo s)
    })
  where
    update dictionary =
      Map.insert package
                 (f (Map.findWithDefault pInfoEmpty package dictionary))
                 dictionary

parserPackageDeclareLocalNameAsDefined :: QualifId -> ParserM ()
parserPackageDeclareLocalNameAsDefined (QualifId package ident) = do
   pos <- parserGetCurrentPosition
   info <- parserGetPackageInfo package
   case Map.lookup ident (pInfoPackageNames info) of
     Just (QualifId qualif ident) ->
       if qualif == package
        then return ()
        else parserFail
               ("La bardeaste feo.\n" ++
                "Se estrolaron los nombres:\n" ++
                "    " ++ ident ++ " (local)\n" ++
                "    " ++ show (QualifId qualif ident))
               pos
     Nothing ->
       parserModifyPackageInfo package (\ info ->
         info {
           pInfoPackageNames =
             Map.insert ident (QualifId package ident) (pInfoPackageNames info)
         }
       )

parserPackageExport :: Position -> [Id] -> ParserM ()
parserPackageExport pos ids = do
    currPackage <- parserGetCurrentPackage
    init currPackage
    mapM_ (exportName currPackage) ids
  where
    init :: PackageName -> ParserM ()
    init currPackage = parserModifyPackageInfo currPackage (\ currInfo ->
      currInfo {
        pInfoPackageExportedNames =
          case pInfoPackageExportedNames currInfo of
            PackageExportAll      -> PackageExportNames []
            PackageExportNames ns -> PackageExportNames ns
      })
    exportName :: PackageName -> Id -> ParserM ()
    exportName currPackage ident = do
      parserModifyPackageInfo currPackage (\ currInfo ->
        currInfo {
          pInfoPackageExportedNames =
            case pInfoPackageExportedNames currInfo of
              PackageExportNames ns -> PackageExportNames (ident : ns)
         }
       )

parserPackageExportedNames :: PackageName -> ParserM [Id]
parserPackageExportedNames package = do
  info <- parserGetPackageInfo package
  case pInfoPackageExportedNames info of
    PackageExportAll      -> return $ Map.keys (pInfoPackageNames info)
    PackageExportNames ns -> return ns

parserPackageImport :: Position -> PackageName -> [(Id, Id)] -> ParserM ()
parserPackageImport pos package idPairs = do
    currPackage <- parserGetCurrentPackage
    currInfo <- parserGetPackageInfo currPackage
    if package `elem` pInfoImportedPackages currInfo
     then parserFail
            ("¿Tenés mierda en la cabeza?\n" ++
             "El paquete\n    " ++ showPackage currPackage ++ "\n" ++
             "ya enchufó al paquete\n    " ++ showPackage package ++ "\n" ++
             "No se puede enchufar dos veces el mismo paquete.")
            pos
     else parserModifyPackageInfo currPackage (\ currInfo ->
            currInfo {
              pInfoImportedPackages =
                package : pInfoImportedPackages currInfo
            }
          )
    mapM_ (importName currPackage package currInfo) idPairs
  where

    importName :: PackageName -> PackageName -> PackageInfo -> (Id, Id) ->
                  ParserM ()
    importName currPackage otherPackage currInfo (otherIdent, currIdent) = do
      assertPackageExports currPackage otherPackage otherIdent

      case Map.lookup currIdent (pInfoPackageNames currInfo) of
        Just (QualifId currPackage currIdent) -> do
          QualifId currPackage currIdent <-
            qualifyInPackage (QualifId currPackage currIdent)
          QualifId otherPackage otherIdent <-
            qualifyInPackage (QualifId otherPackage otherIdent)
          if currPackage == otherPackage && currIdent == otherIdent
           then return ()
           else parserFail
                  ("Tu código no anda ni para atrás.\n" ++
                   "Se estrolaron los nombres:\n" ++
                   "    " ++ show (QualifId otherPackage otherIdent) ++ "\n" ++
                   "    " ++ show (QualifId currPackage currIdent))
                  pos
        Nothing ->
          parserModifyPackageInfo currPackage (\ currInfo ->
            currInfo {
              pInfoPackageNames =
                Map.insert currIdent
                           (QualifId otherPackage otherIdent)
                           (pInfoPackageNames currInfo)
            }
          )

    assertPackageExports :: PackageName -> PackageName -> Id -> ParserM ()
    assertPackageExports currPackage otherPackage otherIdent = do
      exportedNames <- parserPackageExportedNames otherPackage
      if otherIdent `elem` exportedNames
       then return ()
       else parserFail
              ("El paquete\n    " ++ showPackage currPackage ++ "\n" ++
               "está mangueando el símbolo\n    " ++ otherIdent ++ "\n" ++
               "pero el paquete\n    " ++ showPackage package ++ "\n" ++
               "minga que se lo da.")
              pos

parserPackageCheckExportsAreDefined :: Position -> ParserM ()
parserPackageCheckExportsAreDefined pos = do
    currPackage <- parserGetCurrentPackage
    exportedNames <- parserPackageExportedNames currPackage
    currInfo <- parserGetPackageInfo currPackage
    mapM_ (assertDefined currPackage currInfo) exportedNames
  where
    assertDefined :: PackageName -> PackageInfo -> Id -> ParserM ()
    assertDefined package info ident =
      case Map.lookup ident (pInfoPackageNames info) of
        Just _  -> return ()
        Nothing -> parserFail
                     ("El paquete\n    " ++ showPackage package ++ "\n" ++
                      "entrega el símbolo\n    " ++ ident ++ "\n" ++
                      "pero nunca lo define.\n" ++
                      "Arreglalo, querés.")
                     pos

---- Generic parsing utilities

parserMatch :: (Position -> TokenType -> ParserM a) -> ParserM a
parserMatch match = do
    state <- parserGetState
    parserModifyState (\ s -> s { psStream = tail (psStream s)})
    let Token tokType pos : tokens = psStream state
     in match pos tokType

parserDrop1 :: ParserM ()
parserDrop1 = parserMatch (\ _ _ -> return ())

parserExpectAny :: [TokenType] -> ParserM ()
parserExpectAny tokTypes =
    parserMatch (\ pos tokType ->
      if tokType `elem` tokTypes
       then return ()
       else
         parserFail (
           "Mandaste fruta.\n" ++
           (if length tokTypes == 1
            then
               "Esperaba " ++ describeTokenType (head tokTypes) ++ ".\n"
            else
               "Esperaba alguna de estas cosas:\n" ++
               concatMap (\ tt -> "  " ++ describeTokenType tt ++ "\n")
                         tokTypes
           ) ++
           "Pero pusiste " ++ describeTokenType tokType
         )
         pos)

parserExpect :: TokenType -> ParserM ()
parserExpect x = parserExpectAny [x]

parserPeek :: ParserM Token
parserPeek = do
  state <- parserGetState
  return $ head (psStream state)

parserMatchLookahead :: (Position -> TokenType -> ParserM a) -> ParserM a
parserMatchLookahead match = do
  Token tokType pos <- parserPeek
  match pos tokType 

-- Possibly empty list
parseList :: ParserM a -> (TokenType -> Bool) -> ParserM [a]
parseList parse1 isTerminator = do
  Token tokenType _ <- parserPeek
  if isTerminator tokenType
   then return []
   else parseList1 parse1 isTerminator

-- Non-empty list
parseList1 :: ParserM a -> (TokenType -> Bool) -> ParserM [a]
parseList1 parse1 isTerminator = do
  x <- parse1 
  xs <- parseList parse1 isTerminator
  return (x : xs)

-- Possibly empty list
parseSeparatedList :: ParserM a -> TokenType -> (TokenType -> Bool) ->
                      ParserM [a]
parseSeparatedList parse1 separator isTerminator = do
  Token tokenType _ <- parserPeek
  if isTerminator tokenType
   then return []
   else parseSeparatedList1 parse1 separator isTerminator

-- Non-empty list
parseSeparatedList1 :: ParserM a -> TokenType -> (TokenType -> Bool) ->
                       ParserM [a]
parseSeparatedList1 parse1 separator isTerminator = do
  x <- parse1
  Token tokenType _ <- parserPeek
  if tokenType == separator
   then do parserExpect separator
           xs <- parseSeparatedList parse1 separator isTerminator
           return (x : xs)
   else return [x]

---- Specific parsers for the language

qualify :: QualifId -> ParserM QualifId 
qualify (QualifId [] ident) = do
  package <- parserGetCurrentPackage
  qualify (QualifId package ident)
qualify (QualifId qualif ident) = do
    package <- parserGetCurrentPackage
    info <- parserGetPackageInfo package
    if package == qualif || qualif `elem` pInfoImportedPackages info
     then qualifyInPackage (QualifId qualif ident)
     else do
       pos <- parserGetCurrentPosition
       parserFail (
         "Che, qué paja compilar esto.\n" ++
         "El paquete\n    " ++ showPackage package ++ "\n" ++
         "quiere usar el símbolo\n    " ++
         show (QualifId qualif ident) ++ "\n" ++
         "pero no enchufó el paquete\n    " ++
         showPackage qualif
        )
        pos

qualifyInPackage :: QualifId -> ParserM QualifId
qualifyInPackage (QualifId qualif ident) = do
  info <- parserGetPackageInfo qualif
  case Map.lookup ident (pInfoPackageNames info) of
    Just qualifId@(QualifId qualif' _)
      | qualif == qualif' -> return qualifId
      | otherwise         -> qualifyInPackage qualifId
    Nothing       -> return $ QualifId qualif ident

parseUnqualifLowerid :: ParserM Id
parseUnqualifLowerid = parserMatch p
  where
    p _ (T_Lowerid [] ident) = return ident
    p pos tokType = parserFail (
                      "Esperaba un identificador con minúscula " ++
                      "no calificado.\n" ++
                      "Pero pusiste " ++ describeTokenType tokType ++ "."
                    )
                    pos

parseUnqualifUpperid :: ParserM Id
parseUnqualifUpperid = parserMatch p
  where
    p _ (T_Upperid [] ident) = return ident
    p pos tokType = parserFail (
                      "Esperaba un identificador con mayúscula " ++
                      "no calificado.\n" ++
                      "Pero pusiste " ++ describeTokenType tokType ++ "."
                    )
                    pos

parseUnqualifOperator :: ParserM Id
parseUnqualifOperator = parserMatch p
  where
    p _ (T_Operator [] ident) = return ident
    p pos tokType = parserFail (
                      "Esperaba un operador no calificado.\n" ++
                      "Pero pusiste " ++ describeTokenType tokType ++ "."
                    )
                    pos

parseUnqualifId :: ParserM Id
parseUnqualifId = parserMatch p
  where
    p _ (T_Lowerid [] ident)  = return ident
    p _ (T_Upperid [] ident)  = return ident
    p _ (T_Operator [] ident) = return ident
    p pos tokType = parserFail (
                      "Esperaba un identificador no calificado.\n" ++
                      "Pero pusiste " ++ describeTokenType tokType ++ "."
                    )
                    pos

parsePackageName :: ParserM PackageName
parsePackageName = parserMatch p
  where
    p _ (T_Upperid qualif ident) =
      return $ packageFor (QualifId qualif ident)
    p pos tokType = parserFail (
                      "Esperaba el nombre de un paquete.\n" ++
                      "Pero pusiste " ++ describeTokenType tokType ++ "."
                    )
                    pos

parseLowerid :: ParserM QualifId
parseLowerid = parserMatch p
  where
    p _ (T_Lowerid qualif ident) = qualify (QualifId qualif ident)
    p pos tokType = parserFail (
                      "  Había un parser llorando\n" ++
                      "  en la punta de aquel cerro\n" ++
                      "  y sus lágrimas decían:\n" ++
                      "  Syntax error.\n\n" ++
                      "Esperaba un identificador con minúscula.\n" ++
                      "Pero pusiste " ++ describeTokenType tokType ++ "."
                    )
                    pos

parseLoweridOrOperator :: ParserM QualifId
parseLoweridOrOperator = parserMatch p
  where
    p _ (T_Lowerid qualif ident)  = qualify (QualifId qualif ident)
    p _ (T_Operator qualif ident)
      | not (operatorIsConstructor ident) = qualify (QualifId qualif ident)
    p pos tokType = parserFail (
                      "Esperaba un identificador con minúscula.\n" ++
                      "Pero pusiste " ++ describeTokenType tokType ++ "."
                    )
                    pos

parseUpperid :: ParserM QualifId
parseUpperid = parserMatch p
  where
    p _ (T_Upperid qualif ident) = qualify (QualifId qualif ident)
    p pos tokType = parserFail (
                      "Esperaba un identificador con mayúscula.\n" ++
                      "Pero pusiste " ++ describeTokenType tokType ++ "."
                    )
                    pos

parseUpperidOrOperator :: ParserM QualifId
parseUpperidOrOperator = parserMatch p
  where
    p _ (T_Upperid qualif ident)          = qualify (QualifId qualif ident)
    p _ (T_Operator qualif ident)
      | operatorIsConstructor ident       = qualify (QualifId qualif ident)
    p pos tokType = parserFail (
                      "Esperaba un identificador con mayúscula " ++
                       "o un operador.\n" ++
                      "Pero pusiste " ++ describeTokenType tokType ++ "."
                    )
                    pos

parseOperator :: ParserM QualifId
parseOperator = parserMatch p
  where
    p _ (T_Operator qualif ident) = qualify (QualifId qualif ident)
    p pos tokType = parserFail (
                      "Esperaba un operador.\n" ++
                      "Pero pusiste " ++ describeTokenType tokType ++ "."
                    )
                    pos

parseId :: ParserM QualifId
parseId = parserMatch p
  where
    p _ (T_Lowerid qualif ident)  = qualify (QualifId qualif ident)
    p _ (T_Upperid qualif ident)  = qualify (QualifId qualif ident)
    p _ (T_Operator qualif ident) = qualify (QualifId qualif ident)
    p pos tokType = parserFail (
                      "Esperaba un identificador.\n" ++
                      "Pero pusiste " ++ describeTokenType tokType ++ "."
                    )
                    pos

parseTypeConstructorFormalParameters :: ParserM [QualifId]
parseTypeConstructorFormalParameters = do
  Token tokType _ <- parserPeek
  case tokType of
    T_De -> do parserExpect T_De
               parseList1 parseLowerid (not . isTypeFormalParameterFirst)
    _    -> return []
  where
    isTypeFormalParameterFirst :: TokenType -> Bool
    isTypeFormalParameterFirst (T_Lowerid _ _) = True
    isTypeFormalParameterFirst _               = False

parseTypeConstructorArgs :: ParserM [Type]
parseTypeConstructorArgs = do
  Token tokType _ <- parserPeek
  case tokType of
    T_De -> do parserExpect T_De
               parseList1 parseTypeAtom (not . isTypeAtomFirst)
    _    -> return []

isTypeAtomFirst :: TokenType -> Bool
isTypeAtomFirst (T_Lowerid _ _) = True
isTypeAtomFirst (T_Upperid _ _) = True
isTypeAtomFirst T_LParen        = True
isTypeAtomFirst T_LBracket      = True
isTypeAtomFirst _               = False

parseType_ :: Bool -> ParserM Type
parseType_ atom = parserMatch p
  where p pos (T_Lowerid qualif ident) = do
          qualifId <- qualify (QualifId qualif ident)
          args <- if not atom
                   then parseTypeConstructorArgs
                   else return []
          return $ foldl (paAppT pos) (paVarT pos qualifId) args

        p pos (T_Upperid qualif ident)
          | ident == primPtrPrefix = do
             Token tokType _ <- parserPeek
             case tokType of
               T_String _ -> do
                 s <- parseStringConstant
                 return $ primTPtr s
               _ -> return $ primTPtr ""
        p pos (T_Upperid qualif ident) = do
          qualifId <- qualify (QualifId qualif ident)
          args <- if not atom
                   then parseTypeConstructorArgs
                   else return []
          return $ foldl (paAppT pos) (paConstructorT pos qualifId) args
        p pos T_LParen          = do
          ts <- parseSeparatedList parseType T_Comma (== T_RParen) 
          parserExpect T_RParen
          case ts of
            [t] -> return t
            _   -> return $ primTTuple ts
        p pos T_LBracket        = do
          t <- parseType
          parserExpect T_RBracket
          return $ primTList t
        p pos tokType = parserFail (
                          "Esperaba un tipo.\n" ++
                          "Pero pusiste " ++ describeTokenType tokType ++ "."
                        )
                        pos

parseTypeAtom :: ParserM Type
parseTypeAtom = parseType_ True

parseType :: ParserM Type
parseType = do
  t1 <- parseType_ False
  Token tokType _ <- parserPeek
  case tokType of
    T_En -> do parserExpect T_En
               t2 <- parseType
               return (primTFunction t1 t2)
    _    -> return t1

parseTypeConstraints :: ParserM [TypeConstraint]
parseTypeConstraints = do
  Token tokType _ <- parserPeek
  case tokType of
    T_LParen -> do
      parserExpect T_LParen
      constraints <- parseSeparatedList parseTypeConstraint
                                        T_Comma
                                        (== T_RParen)
      parserExpect T_RParen
      return constraints
    _ -> do
      c <- parseTypeConstraint
      return [c]
  where
    parseTypeConstraint :: ParserM TypeConstraint
    parseTypeConstraint = do
      typeClass <- parseUpperid
      parserExpect T_Para
      typeVar   <- parseLowerid
      pos <- parserGetCurrentPosition
      return $ TypeConstraint typeClass (paVarT pos typeVar)

parseConstrainedType :: ParserM ConstrainedType
parseConstrainedType = do
    t <- parseType
    constraints <- parseConstraints
    return $ ConstrainedType constraints t
  where
    parseConstraints :: ParserM [TypeConstraint]
    parseConstraints = do
      Token tokType _ <- parserPeek
      case tokType of
        T_Con -> do parserExpect T_Con
                    parseTypeConstraints
        _     -> return []

parseMaybeConstrainedType :: ParserM (Maybe ConstrainedType)
parseMaybeConstrainedType = do
  Token tokType _ <- parserPeek
  case tokType of
    T_De -> do parserExpect T_De
               t <- parseConstrainedType
               return $ Just t
    _    -> return Nothing

base :: Integer -> Integer -> [Integer]
base b 0 = []
base b n = (n `mod` b) : base b (n `div` b)

-- Parse an atomic expression
parseAtom :: ParserM Expr
parseAtom = parserMatch p
  where
    p pos (T_Lowerid qualif ident) = do
      qualifId <- qualify (QualifId qualif ident)
      return $ paVarE pos qualifId
    p pos (T_Upperid qualif ident) = do
      qualifId <- qualify (QualifId qualif ident)
      -- Check if it is a record creation
      Token tokType _ <- parserPeek
      case tokType of
        T_Cuyo -> parseRecordCreation pos qualifId
        _      -> return $ paConstructorE pos qualifId
    p pos (T_Fixnum n)                =
      return $ paConstantE pos (FixnumC n)
    p pos (T_Integer n)               =
      return $
        paAppE pos
              (paVarE pos (QualifId primPackage primFromDigits)) $
             foldr
               (app2 (paConstructorE pos (QualifId primPackage primListCons)))
               (paConstructorE pos (QualifId primPackage primListNil))
               (map (paConstantE pos . FixnumC)
                    (base (primMaxFixnum + 1) n))
      where
        app2 f = naAppE . naAppE f
    p pos (T_Char c)               =
      return $ paConstantE pos (CharC c)
    p pos (T_String s)             =
        return $
             paAppE pos
                    (paConstructorE pos (QualifId primPackage primString)) $
             foldr
               (app2 (paConstructorE pos (QualifId primPackage primListCons)))
               (paConstructorE pos (QualifId primPackage primListNil))
               (map (paConstantE pos . CharC) s)
      where
        app2 f = naAppE . naAppE f
    p pos T_LParen                 = do
      es <- parseSeparatedList parseExpr T_Comma (== T_RParen) 
      parserExpect T_RParen
      case es of
        [e] -> return e
        _   -> return $ paTupleE pos es
    p pos T_LBracket               = do
      es <- parseSeparatedList parseExpr T_Comma (== T_RBracket) 
      parserExpect T_RBracket
      return $ foldr
        (app2 (paConstructorE pos (QualifId primPackage primListCons)))
        (paConstructorE pos (QualifId primPackage primListNil))
        es
      where app2 f = naAppE . naAppE f
    p pos T_LBrace                 = do
      expr <- parseExpr
      parserExpect T_RBrace
      return $ paLamE pos (QualifId primPackage "_") expr
    p pos tokType = parserFail (
                      "Esperaba una expresión atómica.\n" ++
                      "Pero pusiste " ++ describeTokenType tokType ++
                      ", papafrita."
                    ) pos

parseRecordModificationSuffix :: ParserM (Expr -> Expr)
parseRecordModificationSuffix = do
  parserExpect T_Pero
  fieldNamesValues <- parseList1
                        parseFieldValueDeclaration
                        (/= T_Cuyo)
  return (\ expr0 ->
            foldl (\ expr (fieldName, value) ->
                     naAppE
                       (naAppE (naVarE (setterForField fieldName))
                               expr)
                       value)
                  expr0
                  fieldNamesValues)

parseAtomWithSuffixes :: ParserM Expr
parseAtomWithSuffixes = do
    expr <- parseAtom
    suffixes <- parseList parseSuffix (/= T_Pero)
    return $ foldl (flip ($)) expr suffixes
  where
    parseSuffix :: ParserM (Expr -> Expr)
    parseSuffix = do
      Token tokType _ <- parserPeek
      case tokType of
        T_Pero -> parseRecordModificationSuffix          
        _ -> error "(parseAtomWithSuffixes: esperaba un sufijo)"

-- Parse an application of a function to many arguments
parseApp :: ParserM Expr
parseApp = do
    exprs <- parseList1 parseAtomWithSuffixes (not . isAtomFirst)
    pos <- parserGetCurrentPosition
    return $ foldl1 (paAppE pos) exprs
  where
    isAtomFirst :: TokenType -> Bool
    isAtomFirst (T_Lowerid _ _) = True
    isAtomFirst (T_Upperid _ _) = True
    isAtomFirst (T_Fixnum _)    = True
    isAtomFirst (T_Integer _)   = True
    isAtomFirst (T_Char _)      = True
    isAtomFirst (T_String _)    = True
    isAtomFirst T_LParen        = True
    isAtomFirst T_LBracket      = True
    isAtomFirst T_LBrace        = True
    isAtomFirst _               = False

parserOperatorTable :: ParserM [Operator]
parserOperatorTable = do
  state <- parserGetState
  return $ psOperators state

-- Parse a sequence of expressions involving binary and unary operators,
-- respecting associativity and precedence.
parseBinopExpr :: ParserM Expr
parseBinopExpr = do
    table <- parserOperatorTable
    outerRec $ arrangeOperators table
  where
    outerRec :: [[Operator]] -> ParserM Expr
    outerRec []                    = parseApp
    outerRec table@(ops : moreOps) = do
      if isBinaryOperator (head ops)
       then do
         xs <- binaryRec ops moreOps
         pos <- parserGetCurrentPosition
         return $ uncurry (comb pos . operatorAssociativity . head $ ops) xs
       else unaryRec ops moreOps

    unaryRec :: [Operator] -> [[Operator]] -> ParserM Expr
    unaryRec ops moreOps = do
      Token tokType _ <- parserPeek
      case tokType of
        T_Operator qualif opId
          -> do qualifId <- qualify (QualifId qualif opId)
                if qualifId `elem` map operatorId ops
                 then do parserDrop1
                         e <- unaryRec ops moreOps
                         pos <- parserGetCurrentPosition
                         return $ (paAppE pos) (operatorE qualifId) e
                 else outerRec moreOps
        _ -> outerRec moreOps

    binaryRec :: [Operator] -> [[Operator]] ->
                 ParserM (Expr, [(QualifId, Expr)])
    binaryRec ops moreOps = do
      x               <- outerRec moreOps
      Token tokType _ <- parserPeek
      case tokType of
        T_Operator qualif opId
          -> do qualifId <- qualify (QualifId qualif opId)
                if qualifId `elem` map operatorId ops
                 then do parserDrop1
                         (y, zs) <- binaryRec ops moreOps
                         return (x, (qualifId, y) : zs)
                 else return (x, [])
        _ -> return (x, [])

    arrangeOperators = groupByPrecedence .  sortByPrecedence

    sortByPrecedence  = sortBy (compare `on` operatorPrecedence)
    groupByPrecedence = groupBy ((==) `on` operatorPrecedence)

    comb :: Position -> Associativity -> Expr -> [(QualifId, Expr)] -> Expr
    comb pos AssocLeft  = combLeft pos
    comb pos AssocRight = combRight pos

    combLeft :: Position -> Expr -> [(QualifId, Expr)] -> Expr
    combLeft pos x []             = x
    combLeft pos x ((op, y) : zs) =
      combLeft pos (paAppE pos (paAppE pos (operatorE op) x) y) zs

    combRight :: Position -> Expr -> [(QualifId, Expr)] -> Expr
    combRight pos x []             = x
    combRight pos x ((op, y) : zs) =
      paAppE pos (paAppE pos (operatorE op) x) (combRight pos y zs)

parsePattern_ :: ParserM Expr -> ParserM Pattern
parsePattern_ expressionParser = do
    e <- expressionParser
    p <- expressionToPattern e
    if evalState (checkLinear p) []
     then return p
     else do
       pos <- parserGetCurrentPosition
       parserFail (
         "¿Quién carajo te creés que sos?\n" ++
         "No puede haber variables repetidas en el patrón.\n" ++
         "El patrón tiene que ser lineal."
        )
        pos
  where
    expressionToPattern :: Expr -> ParserM Pattern
    expressionToPattern (AVarE ann (QualifId _ "_")) =
      return $ AAnyP ann
    expressionToPattern (AVarE ann x) =
      return $ AVarP ann x
    expressionToPattern (AConstantE ann c) =
      return $ AConstantP ann c
    expressionToPattern (ATupleE ann es) = do
      ps <- mapM expressionToPattern es
      return $ ATupleP ann ps
    expressionToPattern e =
      expressionToApplicativePattern e []

    expressionToApplicativePattern :: Expr -> [Pattern] -> ParserM Pattern
    expressionToApplicativePattern (AAppE _ f x) ps    = do
      p <- expressionToPattern x
      expressionToApplicativePattern f (p : ps)
    expressionToApplicativePattern (AConstructorE ann c) ps = do
      return $ AConstructorP ann c ps
    expressionToApplicativePattern e _ = do
      pos <- parserGetCurrentPosition
      parserFail (
        "La concha tuya.\n" ++
        "La expresión no constituye un patrón válido."
       )
       pos

    checkLinear :: Pattern -> State [QualifId] Bool
    checkLinear (AVarP _ x) = do
      xs <- get
      if x `elem` xs
       then return False
       else do modify (x :)
               return True
    checkLinear (AConstructorP _ c xs) = do
      ys <- mapM checkLinear xs
      return $ and ys
    checkLinear (AConstantP _ _) = return True
    checkLinear (ATupleP _ xs) = do
      ys <- mapM checkLinear xs
      return $ and ys
    checkLinear (AAnyP _) = return True

parsePatternAtom :: ParserM Pattern
parsePatternAtom = parsePattern_ parseAtom

parsePattern :: ParserM Pattern
parsePattern = parsePattern_ parseExpr

parseMatchBranch :: ParserM MatchBranch
parseMatchBranch = do
  parserExpect T_Si
  Token tokType _ <- parserPeek
  p <- case tokType of
         T_No -> do parserExpect T_No
                    pos <- parserGetCurrentPosition
                    return $ paAnyP pos
         _    -> parsePattern
  parserExpect T_Da
  e <- parseExpr
  return $ MatchBranch p e

parseIfThenElse :: ParserM Expr
parseIfThenElse = do
    pos <- parserGetCurrentPosition
    parserExpect T_Si
    alternatives <- parseList parseElseIfBranch (== T_No)
    parserExpect T_No
    parserExpect T_Da
    elseBranch <- parseExpr
    return $ matchFromBranches alternatives elseBranch
  where
    parseElseIfBranch :: ParserM (Position, Expr, Expr)
    parseElseIfBranch = do
      pos <- parserGetCurrentPosition
      cond <- parseExpr
      parserExpect T_Da
      thenBranch <- parseExpr
      parserExpect T_Si
      return (pos, cond, thenBranch)
    matchFromBranches :: [(Position, Expr, Expr)] -> Expr -> Expr
    matchFromBranches [] elseBranch = elseBranch
    matchFromBranches ((pos, cond, thenBranch) : alternatives) elseBranch =
      paMatchE pos cond [
        MatchBranch
          (paConstructorP pos (QualifId primPackage primBoolTrue) [])
          thenBranch,
        MatchBranch
          (paAnyP pos)
          (matchFromBranches alternatives elseBranch) 
      ]

monadicLet :: Position -> [Declaration] -> Expr -> ParserM Expr
monadicLet pos [] body = return body
monadicLet pos (AValueD ann x typ expr : decls) body = do
    expr' <- annotate typ expr
    body' <- monadicLet pos decls body
    return $
      paAppE pos
        (paAppE pos
          (paVarE pos (QualifId primPackage primMonadBind))
          expr')
        (paLamE pos x body')
  where
    annotate :: Maybe ConstrainedType -> Expr -> ParserM Expr
    annotate Nothing    x = return x
    annotate (Just typ) x = do
      y <- parserFreshQualifId
      return $ paLetE pos [paValueD pos y (Just typ) x] (paVarE pos y)

parseMonadicValueDeclaration :: ParserM Declaration
parseMonadicValueDeclaration = do
  parserExpect T_Che
  Token tokType _ <- parserPeek
  case tokType of
    T_ArticuloD -> parseValueDeclaration
    _ -> do
      pos <- parserGetCurrentPosition
      expr <- parseExpr
      return (paValueD pos (QualifId primPackage "_") Nothing expr)

-- Parse an expression without type annotations
parseBareExpr :: ParserM Expr
parseBareExpr = parserMatchLookahead p
  where
    p pos T_ArticuloD    = do
      parserExpect T_ArticuloD
      Token tokType _ <- parserPeek
      case tokType of
        T_Que -> do
          parserExpect T_Que
          parseMatchingDeclaration
        T_Operator _ _ -> do
          op@(QualifId _ opname) <- parseOperator
          if operatorIsConstructor opname
           then return $ paConstructorE pos op
           else return $ paVarE pos op
        _ ->
          parserFail (
            "¿Me estás jodiendo?\n" ++
            "Un artículo determinado tiene que " ++
            "ir seguido de 'que' o de un operador."
           )
           pos
    p pos T_Mirar        = do
      parserExpect T_Mirar
      x <- parseExpr
      branches <- parseList parseMatchBranch (== T_Boludo)
      parserExpect T_Boludo
      return $ paMatchE pos x branches
    p pos T_Ponele       = do
      parserExpect T_Ponele
      parserExpect T_Que
      declarations <- parseList parseValueDeclaration (== T_En)
      parserExpect T_En
      body <- parseExpr
      return $ paLetE pos declarations body
    p pos T_Che       = do
      declarations <- parseList parseMonadicValueDeclaration (/= T_Che)
      parserExpect T_En
      body <- parseExpr
      monadicLet pos declarations body
    p pos T_Ante        = do
      parserExpect T_Ante
      ids <- parseList parseLowerid (== T_Da)
      parserExpect T_Da
      body <- parseExpr
      return $ foldr (paLamE pos) body ids
    p pos T_Si          = do
      parseIfThenElse
    p _ _ = parseBinopExpr

-- Parser an expression, perhaps with type annotations
parseExpr :: ParserM Expr
parseExpr = do
  expr <- parseBareExpr
  typ <- parseMaybeConstrainedType
  case typ of
    Nothing  -> return expr
    Just typ -> do
      pos <- parserGetCurrentPosition
      id <- parserFreshQualifId
      return (paLetE pos [paValueD pos id (Just typ) expr] (paVarE pos id))

parseInteger :: ParserM Integer
parseInteger = parserMatch p
  where
    p _ (T_Integer n) = return n
    p pos tokType     = parserFail (
                          "Pero mirá lo que hacés, animal.\n" ++
                          "Esperaba un número.\n" ++
                          "Pero pusiste " ++ describeTokenType tokType ++ "."
                        ) pos

parseStringConstant :: ParserM String
parseStringConstant = parserMatch p
  where
    p _ (T_String s) = return s
    p pos tokType    = parserFail (
                         "Qué paja compilar tu código.\n" ++
                         "Esperaba una cadena.\n" ++
                         "Pero pusiste " ++ describeTokenType tokType ++ "."
                       )
                       pos

parserDeclareOperator :: Position -> Operator -> ParserM ()
parserDeclareOperator pos op = do
    table <- parserOperatorTable 
    insertOperator table
  where
    insertOperator table
      | not . null . similarOperators $ table = 
          parserFail (
            "Guarda que el operador " ++ show (operatorId op) ++
            " ya existe."
          ) pos
      | ambiguousFixity table = 
          parserFail (
            "Te zarpaste.\n" ++
            "No se pueden declarar distintas asociatividades\n" ++
            "para el nivel de precedencia " ++
            show (operatorPrecedence op) ++ "."
          )
          pos
      | otherwise =
          parserModifyState (\ s -> s { psOperators = op : table })
    similarOperators =
      filter (\ op' ->
        operatorId op' == operatorId op &&
        isBinaryOperator op' == isBinaryOperator op)
    ambiguousFixity =
      not . null .
      filter (\ op' ->
        operatorPrecedence op' == operatorPrecedence op &&
        operatorAssociativity op' /= operatorAssociativity op)

parseConstructorDeclarations :: ParserM [ConstructorDeclaration]
parseConstructorDeclarations =
    parseList parseConstructorDeclaration (not . isBien)
  where
    isBien :: TokenType -> Bool
    isBien T_Bien = True
    isBien _      = False
    parseConstructorDeclaration :: ParserM ConstructorDeclaration
    parseConstructorDeclaration = do
      parserExpect T_Bien
      qualifName <- parseUpperidOrOperator
      parserPackageDeclareLocalNameAsDefined qualifName
      types <- parseList parseTypeAtom (not . isTypeAtomFirst)
      return $ ConstructorDeclaration qualifName types

parseValueDeclaration :: ParserM Declaration
parseValueDeclaration = do
  parserExpect T_ArticuloD
  pos <- parserGetCurrentPosition
  qualifId <- parseLoweridOrOperator
  typ <- parseMaybeConstrainedType
  val <- parseValueDeclarationBody
  return $ paValueD pos qualifId typ val

parseOptionalWhereClause :: Expr -> ParserM Expr
parseOptionalWhereClause expr = do
   Token tokType pos <- parserPeek
   case tokType of
     T_Donde -> do
       parserExpect T_Donde
       declarations <- parseList parseValueDeclaration (== T_Boludo)
       parserExpect T_Boludo
       return $ paLetE pos declarations expr
     _ ->
       return expr

parseValueDeclarationBody :: ParserM Expr
parseValueDeclarationBody = do
    Token tokType _ <- parserPeek
    case tokType of
      T_Dado  -> parseMatchingDeclaration
      _       -> do parserExpect T_Es
                    expr <- parseExpr
                    expr' <- parseOptionalWhereClause expr
                    return expr'

parseMatchingDeclaration :: ParserM Expr
parseMatchingDeclaration = do
    branches <- parseList branch (not . isMatchingDeclarationFirst)
    let nargs = length (fst (head branches))
     in if and (map ((== nargs) . length . fst) branches)
         then do 
           pos <- parserGetCurrentPosition
           ids <- mapM (const parserFreshQualifId) [1..nargs]
           return $ foldr
             (paLamE pos)
             (paMatchE
                pos
                (paTupleE pos (map (paVarE pos) ids))
                (map (\ (pats, expr) ->
                         MatchBranch (paTupleP pos pats) expr) branches))
             ids
         else do
           pos <- parserGetCurrentPosition
           parserFail (
              "Mandaste cualquiera.\n" ++
              "Las definiciones de una misma función deberían tener\n" ++
              "todas la misma cantidad de parámetros."
             )
             pos
  where
    branch :: ParserM ([Pattern], Expr)
    branch = do parserExpect T_Dado
                pats <- parseList parsePatternAtom (`elem` [T_Da, T_Si])
                Token tokType pos <- parserPeek
                case tokType of
                  T_Da -> parserExpect T_Da
                  T_Si -> return ()
                  _    -> parserFail "Esperaba 'da' o 'si'." pos
                expr <- parseExpr
                expr' <- parseOptionalWhereClause expr
                return (pats, expr')
    isMatchingDeclarationFirst :: TokenType -> Bool
    isMatchingDeclarationFirst T_Dado  = True
    isMatchingDeclarationFirst _       = False

parseUnqualifIdAs :: ParserM (Id, Id)
parseUnqualifIdAs = do
  id <- parseUnqualifId
  Token tokType _ <- parserPeek
  case tokType of
    T_Como -> do parserExpect T_Como
                 id' <- parseUnqualifId
                 return (id, id')
    _      -> return (id, id)

checkInstanceTypeWellFormed :: ConstrainedType -> ParserM ()
checkInstanceTypeWellFormed ctype@(ConstrainedType _ typ) = do
    checkType typ
  where
    checkType :: Type -> ParserM ()
    checkType (AAppT _ t1 t2)  = do
      checkIsVarT t2
      checkType t1
    checkType (AConstructorT _ _)  = return ()
    checkType _                    = failmsg

    checkIsVarT (AVarT _ _) = return ()
    checkIsVarT _           = failmsg
      
    failmsg :: ParserM ()
    failmsg = do
      pos <- parserGetCurrentPosition
      parserFail ("Te desubicaste.\n" ++
                  "No se puede encarnar una cualidad para " ++
                  "el tipo\n    " ++ show typ ++ "\n" ++
                  "Tiene que ser de la forma\n    " ++
                  "Bolsa de coso1 ... cosoN\n" ++
                  "donde Bolsa no puede ser un sinónimo.")
                 pos

parseFieldValueDeclaration :: ParserM (QualifId, Expr)
parseFieldValueDeclaration = do
  parserExpect T_Cuyo
  field <- parseLowerid
  parserExpect T_Es
  expr <- parseExpr
  return (field, expr)

setterForField :: QualifId -> QualifId
setterForField fieldName =
  QualifId
    primPackage
    ("{setter|" ++ mangleQualifId fieldName ++ "}")

parseRecordCreation :: Position -> QualifId -> ParserM Expr
parseRecordCreation pos recordName = do
    fieldNamesValues <- parseList1
                          parseFieldValueDeclaration
                          (/= T_Cuyo)
    let fieldNames  = map fst fieldNamesValues in do
      state <- parserGetState
      case Map.lookup recordName (psRecordFields state) of
        Nothing -> parserFail
                     ("Te fuiste a la mierda.\n" ++
                      "El registro " ++ show recordName ++
                      " no fue declarado.") pos
        Just expectedFieldNames -> do
          if repeatedFieldNames fieldNames
           then parserFail
                     ("Te fuiste al carajo.\n" ++
                      "La construcción de un registro no puede " ++
                      "incluir campos repetidos.") pos
           else return ()
          if not (sameFieldNames expectedFieldNames fieldNames)
           then parserFail (
                  "Measte fuera del tarro.\n" ++
                  "Los nombres de los campos declarados no coinciden\n" ++
                  "con los proporcionados al construir el registro\n    " ++
                  show recordName ++ "\n" ++
                  "Campos esperados:\n    " ++
                  joinS ", " (map showBareId expectedFieldNames) ++ "\n" ++
                  "Campos proporcionados:\n    " ++
                  joinS ", " (map showBareId fieldNames) ++ "\n"
                )
                pos
           else return ()
          return
            (foldl naAppE
                   (naConstructorE recordName)
                   (sortedValues expectedFieldNames fieldNamesValues))
  where
    repeatedFieldNames :: [QualifId] -> Bool
    repeatedFieldNames fs = length (nub fs) < length fs
    sameFieldNames :: [QualifId] -> [QualifId] -> Bool
    sameFieldNames efs fs = all (`elem` fs) efs &&
                            all (`elem` efs) fs
    sortedValues :: [QualifId] -> [(QualifId, Expr)] -> [Expr]
    sortedValues efs fs = map (\ name -> fromJust (lookup name fs)) efs

parseRecordDeclaration :: Position -> QualifId -> [QualifId] ->
                          ParserM [Declaration]
parseRecordDeclaration pos recordName args = do
    parserExpect T_Tiene
    fieldDecls <- parseList parseFieldDeclaration (== T_Boludo)
    parserExpect T_Boludo
    let fieldTypes = map fieldType fieldDecls
        fieldNames = map fieldName fieldDecls
        constructorDecl = ConstructorDeclaration recordName fieldTypes
     in do
       state <- parserGetState
       case Map.lookup recordName (psRecordFields state) of
         Just _  -> parserFail (
                       "El registro " ++ show recordName ++
                       " ya había sido declarado."
                    )
                    pos
         Nothing -> parserModifyState (\ state ->
                      state {
                        psRecordFields =
                          Map.insert recordName fieldNames
                                     (psRecordFields state)
                      })
       classDeclList <- mapM maybeClassDeclaration fieldDecls
       return ([paDatatypeD pos recordName args [constructorDecl]] ++
               concat classDeclList ++
               instanceDeclarations fieldDecls)
  where
    fieldName :: FieldDeclaration -> QualifId
    fieldName (FieldDeclaration name _) = name

    fieldType :: FieldDeclaration -> Type
    fieldType (FieldDeclaration _ t) = t

    maybeClassDeclaration :: FieldDeclaration -> ParserM [Declaration]
    maybeClassDeclaration (FieldDeclaration fieldName typ) = do
      state <- parserGetState
      case Map.lookup fieldName (psFields state) of
        Just _  -> return [] -- class already declared
        Nothing ->
          let decl = [classDeclaration fieldName typ] in do
            parserModifyState (\ state ->
              state {
                psFields = Map.insert fieldName () (psFields state)
              })
            return decl

    classDeclaration :: QualifId -> Type -> Declaration
    classDeclaration fieldName fieldType =
        paClassD
          pos
          (_accessorClass fieldName)
          _record
          [
            MethodDeclaration (_getter fieldName) getterType,
            MethodDeclaration (_setter fieldName) setterType
          ]
      where
        getterType :: ConstrainedType
        getterType = ConstrainedType [] $
                       primTFunction
                         (recordTypeFor (naVarT _record))
                         fieldType

        setterType :: ConstrainedType
        setterType = ConstrainedType [] $
                       primTFunction
                         (recordTypeFor (naVarT _record))
                         (primTFunction
                           fieldType
                           (recordTypeFor (naVarT _record)))

    instanceDeclarations :: [FieldDeclaration] -> [Declaration]
    instanceDeclarations fieldDecls =
        zipWith (\ f i -> instanceDeclaration f i n)
                fieldDecls
                [0..]
      where n = length fieldDecls

    instanceDeclaration :: FieldDeclaration -> Int -> Int -> Declaration
    instanceDeclaration (FieldDeclaration fieldName typ) i n = do
        paInstanceD
          pos
          (_accessorClass fieldName)
          (ConstrainedType [] $ naConstructorT recordName)
          [
            MethodImplementation (_getter fieldName) getterImpl,
            MethodImplementation (_setter fieldName) setterImpl
          ]
      where
        getterImpl :: Expr
        getterImpl = naLamE _record
                       (naMatchE (naVarE _record) [
                         MatchBranch
                           (naConstructorP
                              recordName
                              (map naVarP (_fields n)))
                           (naVarE (_field i))
                       ])

        setterImpl :: Expr
        setterImpl = naLamE _record $ naLamE _value
                       (naMatchE (naVarE _record) [
                         MatchBranch
                           (naConstructorP
                              recordName
                              (map naVarP (_fields n)))
                           (foldl naAppE
                             (naConstructorE recordName)
                             (map newValue [0..n - 1]))
                       ])
          where
            newValue j | i == j    = naVarE _value
                       | otherwise = naVarE (_field j)

    recordTypeFor :: Type -> Type
    recordTypeFor c = foldl naAppT c (map naVarT args)

    _accessorClass :: QualifId -> QualifId
    _accessorClass fieldName =
      QualifId
        primPackage
        ("{accessor|" ++ mangleQualifId fieldName ++ "}")

    _record :: QualifId
    _record = QualifId primPackage "{record}"

    _value :: QualifId
    _value = QualifId primPackage "{value}"

    _getter :: QualifId -> QualifId
    _getter fieldName = fieldName

    _setter :: QualifId -> QualifId
    _setter fieldName = setterForField fieldName

    _field :: Int -> QualifId
    _field i = QualifId primPackage ("{field|" ++ show i ++ "}")

    _fields :: Int -> [QualifId]
    _fields n = map _field [0..n - 1]

----

data FeatureRestriction = FeaturePresent FeatureName
                        | FeatureAbsent FeatureName
  deriving Show

parsePragmaIf :: ParserM [Declaration]
parsePragmaIf = do
    parserExpect T_SI
    parserExpect T_LParen
    featureRestrictions <- parseSeparatedList
                             parseFeature
                             T_Comma
                             (== T_RParen)
    parserExpect T_RParen
    cond <- restrictionsHold featureRestrictions
    if cond
     then do
       decls <- parseList parseDeclaration (== T_BOLUDO)
       parserExpect T_BOLUDO
       return $ concat decls
     else do
       skipTokens 1
       return []
  where
    restrictionsHold :: [FeatureRestriction] -> ParserM Bool
    restrictionsHold restrictions = do
        state <- get
        let features = parserOptionsFeatures (psOptions state)
         in return $ all (holds features) restrictions
      where
        holds :: [FeatureName] -> FeatureRestriction -> Bool
        holds features (FeaturePresent f) = f `elem` features
        holds features (FeatureAbsent f)  = f `notElem` features

    skipTokens :: Integer -> ParserM ()
    skipTokens n = do
      Token tokType pos <- parserPeek
      case tokType of
        T_SI -> do
          parserDrop1
          skipTokens (n + 1)
        T_BOLUDO -> do
          parserDrop1
          if n <= 0
           then parserFail "Demasiados boludos." pos
           else (if n == 1
                  then return ()
                  else skipTokens (n - 1))
        _ -> do
          parserDrop1
          skipTokens n

    parseFeature :: ParserM FeatureRestriction
    parseFeature = do
      Token tokType pos <- parserPeek
      restriction <-
        case tokType of
          T_Operator _ "+" -> do
            parserDrop1
            return FeaturePresent
          T_Operator _ "-" -> do
            parserDrop1
            return FeatureAbsent
          _ -> do
            parserFail (
                "Esperaba un + o un - para el requisito de la condición.\n" ++
                "Por ejemplo:\n" ++
                "SI (+Banana, -Manzana)\n" ++
                "  ...\n" ++
                "BOLUDO\n"
              ) pos
      feature <- parseUnqualifUpperid 
      return $ restriction feature

parseForeignLang :: Position -> ParserM ForeignLang
parseForeignLang pos = do
  lang <- parseUnqualifUpperid
  let languages = [("C", ForeignLangC),
                   ("Py", ForeignLangPy),
                   ("Jvm", ForeignLangJvm)]
   in
     case lookup lang languages of
       Just foreignLang -> return foreignLang
       Nothing ->
           parserFail (
               "Tenías que poner un lenguaje gringo válido.\n" ++
               "Lenguajes gringos reconocidos:\n" ++
               joinS "\n" (map (("    " ++) . fst) languages) ++ "\n" ++
               "Mirá lo que pusiste imbécil:\n" ++
               "    " ++ lang
             ) pos

parsePragmaForeign :: Position -> ParserM [Declaration]
parsePragmaForeign pos = do
  parserExpect T_GRINGO
  lang <- parseForeignLang pos 
  decl <- parseStringConstant
  modify (\ state -> state {
    psPragmas = psPragmas state ++ [ForeignPragma lang decl]
  })
  return []

----

parseDeclaration :: ParserM [Declaration]
parseDeclaration = parserMatchLookahead p
  where
    p pos (T_Paquete packageName) = do
       parserDrop1
       parserPushPackage packageName
       decls <- parseList parseDeclaration (== T_FinPaquete)
       parserExpect T_FinPaquete
       parserPackageCheckExportsAreDefined pos
       parserPopPackage
       return (concat decls)
    p pos T_Enchufar = do
       parserExpect T_Enchufar
       package <- parsePackageName
       Token tokType pos <- parserPeek
       idPairs <-
         case tokType of
            T_LParen -> do
              parserExpect T_LParen
              idPairs <- parseSeparatedList
                           parseUnqualifIdAs
                           T_Comma
                           (== T_RParen)
              parserExpect T_RParen
              return idPairs
            _        -> do
              ids <- parserPackageExportedNames package
              return (zip ids ids)
       parserPackageImport pos package idPairs
       return []
    p pos T_Entregar = do
       parserExpect T_Entregar
       parserExpect T_LParen
       ids <- parseSeparatedList parseUnqualifId T_Comma (== T_RParen)
       parserExpect T_RParen
       parserPackageExport pos ids
       return []
    p pos T_Chirimbolo = do
       parserExpect T_Chirimbolo
       associativity <- parseAssociativity pos
       precedence    <- parseInteger
       opId          <- parseUnqualifOperator
       qualifId      <- qualify (QualifId [] opId)
       parserDeclareOperator pos (Operator associativity precedence qualifId)
       return []
    p pos T_ArticuloD = do
       decl <- parseValueDeclaration
       let AValueD _ qualifId _ _ = decl in do
         parserPackageDeclareLocalNameAsDefined qualifId
         return [decl]
    p pos T_ArticuloI = do
       parserExpect T_ArticuloI
       qualifId <- parseUpperid
       args <- parseTypeConstructorFormalParameters
       parserPackageDeclareLocalNameAsDefined qualifId
       Token tokType1 _ <- parserPeek
       case tokType1 of
         T_Es -> do
           parserExpect T_Es
           Token tokType2 _ <- parserPeek
           case tokType2 of
             T_Bien -> do
               constructorDecls <- parseConstructorDeclarations
               return [paDatatypeD pos qualifId args constructorDecls]
             _    -> do
               t <- parseType
               return [paTypeD pos qualifId args t]
         T_Tiene -> parseRecordDeclaration pos qualifId args
         _ -> parserFail ("Se esperaba una declaración de tipo, ya sea:\n" ++
                          "- sinónimo\n" ++
                          "  (un Nombre es Cadena)\n" ++
                          "- tipo inductivo\n" ++
                          "  (un Gusto es\n" ++
                          "      bien Frutilla\n" ++
                          "      bien Chocolate)\n" ++
                          "- registro\n" ++
                          "  (un Punto tiene\n" ++
                          "     la x de Numerito\n" ++
                          "     el y de Numerito\n" ++
                          "   boludo)")
                         pos
    p pos T_Cualidad = do
      parserExpect T_Cualidad
      qualifCls <- parseUpperid
      parserPackageDeclareLocalNameAsDefined qualifCls
      parserExpect T_Para
      param <- parseLowerid 
      methods <- parseList parseMethodDeclaration (== T_Boludo)
      parserExpect T_Boludo
      return [paClassD pos qualifCls param methods]
    p pos T_Encarnar = do
      parserExpect T_Encarnar
      cls <- parseUpperid
      parserExpect T_Para
      param <- parseConstrainedType
      checkInstanceTypeWellFormed param
      methods <- parseList parseMethodImplementation (== T_Boludo)
      parserExpect T_Boludo
      return [paInstanceD pos cls param methods]
    p pos T_Gringo = do
      parserExpect T_Gringo
      foreignLang <- parseForeignLang pos
      foreignName <- parseStringConstant
      qualifId <- parseLowerid
      parserExpect T_De
      typ <- parseType
      return [paForeignD pos foreignLang foreignName qualifId typ]
    p pos (T_Operator qualif ident) =
      parserFail ("Operador " ++ ident ++ " ¡no existís papá!") pos
    p pos T_SI = do
      parsePragmaIf
    p pos T_GRINGO =
      parsePragmaForeign pos
    p pos tokenType =
      parserFail (
        "Mandaste cualquiera: " ++ describeTokenType tokenType ++ ".\n" ++
        "Esperaba una declaración."
      )
      pos

    parseAssociativity :: Position -> ParserM Associativity
    parseAssociativity pos = do
       a <- parseUnqualifLowerid
       case a of
        "zurdo"   -> return AssocLeft
        "diestro" -> return AssocRight
        "prefijo" -> return AssocPrefix
        _ ->
            parserFail (
              "Tenías que poner una asociatividad válida.\n" ++
              "Asociatividades reconocidas:\n" ++
              "    diestro, prefijo, zurdo\n" ++
              "Mirá lo que pusiste imbécil:\n" ++
              "    " ++ a
            )
            pos

    isPackageHeaderFirst :: TokenType -> Bool
    isPackageHeaderFirst T_Enchufar   = True
    isPackageHeaderFirst T_Entregar   = True
    isPackageHeaderFirst T_Chirimbolo = True
    isPackageHeaderFirst _            = False

parseFieldDeclaration :: ParserM FieldDeclaration
parseFieldDeclaration = do
  parserExpect T_ArticuloD
  qualifId <- parseLoweridOrOperator
  parserPackageDeclareLocalNameAsDefined qualifId
  parserExpect T_De
  typ <- parseType
  return (FieldDeclaration qualifId typ)

parseMethodDeclaration :: ParserM MethodDeclaration
parseMethodDeclaration = do
  parserExpect T_ArticuloD
  qualifId <- parseLoweridOrOperator
  parserPackageDeclareLocalNameAsDefined qualifId
  param <- parseMaybeConstrainedType
  case param of
    Nothing -> do
      pos <- parserGetCurrentPosition
      parserFail (
        "La cagaste.\n" ++
        "La declaración del método\n    " ++ showBareId qualifId ++ "\n" ++
        "tiene que venir acompañada de su tipo."
       )
       pos
    Just constrainedType ->
      return (MethodDeclaration qualifId constrainedType)

parseMethodImplementation :: ParserM MethodImplementation
parseMethodImplementation = do
    AValueD _ var typ val <- parseValueDeclaration
    case typ of
      Just _  -> do
        pos <- parserGetCurrentPosition
        parserFail (
          "Te mandaste un moco.\n" ++
          "La implementación del método\n    " ++ showBareId var ++ "\n" ++
          "no debe venir acompañada de su tipo."
         )
         pos
      Nothing -> return ()
    return $ MethodImplementation var val

parseProgram :: PackageName -> Id -> ParserM Expr
parseProgram packageName mainName = do
  pos <- parserGetCurrentPosition
  decls <- parseList parseDeclaration (== T_EOF)
  return $ paLetE pos (concat decls)
                      (paVarE pos (QualifId packageName mainName))

parseFromString :: ParserOptions -> PackageName -> Id -> String ->
                   Either String Expr
parseFromString parserOptions package mainName contents = do
    tokens <- tokenize package contents
    let tokens' = [Token (T_Paquete package) pos] ++
                  init tokens ++
                  [Token T_FinPaquete pos] ++
                  [last tokens]
      in fmap snd $
         runParserM parserOptions tokens' $
         parseProgram package mainName
  where
    pos = Position package "" 0 0

parseFromStringOrFail :: ParserOptions -> PackageName -> Id -> String -> Expr
parseFromStringOrFail parserOptions package mainName contents =
    orFail
      (parseFromString parserOptions package mainName contents)

parsePackagesWithPragmas :: ParserOptions -> [(PackageName, [Token])] ->
                            Id -> Either String ([Pragma], Expr)
parsePackagesWithPragmas parserOptions packages mainName =
    runParserM parserOptions tokens $
    parseProgram packageName mainName
  where
    -- We drop all the T_EOF's but the last one.
    -- The content of each package is wrapped between T_Paquete...T_FinPaquete
    tokens :: [Token]
    tokens = concat (map (uncurry wrap) packages) ++
             [last . snd . last $ packages]
    packageName :: PackageName
    packageName = fst (last packages)
    wrap :: PackageName -> [Token] -> [Token]
    wrap package tokens = [Token (T_Paquete package) pos] ++
                          init tokens ++
                          [Token T_FinPaquete pos]
      where pos = Position package "" 0 0

parsePackages :: ParserOptions -> [(PackageName, [Token])] -> Id ->
                 Either String Expr
parsePackages parserOptions packages mainName =
    fmap snd $
    parsePackagesWithPragmas parserOptions packages mainName

parsePackagesOrFail :: ParserOptions -> [(PackageName, [Token])] -> Id -> Expr
parsePackagesOrFail parserOptions packages mainName =
  orFail (parsePackages parserOptions packages mainName)

