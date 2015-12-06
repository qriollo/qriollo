
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

module Lexer(
        packageFor,
        Token(..),
        TokenType(..),
        tokenize,
        describeTokenType,
    ) where

import Control.Monad.Trans.State.Lazy(
        StateT(..), get, modify, evalStateT,
    )
import Data.Char

import ExpressionE(PackageName, Id, QualifId(..), showPackage)
import Position(Position(..), describePosition, showNearbyCode, updatePosition)

packageFor :: QualifId -> PackageName
packageFor (QualifId parents ident) = parents ++ [ident]

data TokenType = T_EOF
               | T_Lowerid PackageName Id
               | T_Upperid PackageName Id
               | T_Operator PackageName Id
               | T_Fixnum Integer
               | T_Char Char
               | T_Integer Integer
               | T_String String
               -- Keywords
               | T_Ante
               | T_ArticuloD
               | T_ArticuloI
               | T_Bien
               | T_Boludo
               | T_Chirimbolo
               | T_Che
               | T_Como
               | T_Con
               | T_Cualidad
               | T_Cuyo
               | T_Da
               | T_Dado
               | T_De
               | T_Donde
               | T_En
               | T_Encarnar
               | T_Enchufar
               | T_Entregar
               | T_Es
               | T_Gringo
               | T_Mirar
               | T_Para
               | T_Pero
               | T_Ponele
               | T_Que
               | T_Si
               | T_Tiene
               | T_No
               -- Preprocessor keywords
               | T_BOLUDO
               | T_GRINGO
               | T_SI
               -- Symbols
               | T_LParen
               | T_RParen
               | T_LBracket
               | T_RBracket
               | T_LBrace
               | T_RBrace
               | T_Comma
               -- Internal tokens
               | T_Paquete PackageName
               | T_FinPaquete
  deriving (Show, Eq)

describeTokenType :: TokenType -> String
describeTokenType T_EOF = "el final del archivo"
describeTokenType (T_Lowerid package id) =
  "un identificador con minúscula (" ++ show (QualifId package id) ++ ")"
describeTokenType (T_Upperid package id) =
  "un identificador con mayúscula (" ++ show (QualifId package id) ++ ")"
describeTokenType (T_Operator package id) =
  "un chirimbolo (" ++ show (QualifId package id) ++ ")"
describeTokenType (T_Fixnum n) =
  "un numerito (" ++ show n ++ "#)"
describeTokenType (T_Char c) =
  "una letra (" ++ show c ++ ")"
describeTokenType (T_Integer n) =
  "un número (" ++ show n ++ ")"
describeTokenType (T_String s) =
  "un texto (" ++ show s ++ ")"
describeTokenType T_Ante        = "'ante'"
describeTokenType T_ArticuloD   = "un artículo determinado ('el', 'la', ...)"
describeTokenType T_ArticuloI   = "un artículo indeterminado ('un', 'una', ...)"
describeTokenType T_Bien        = "'bien'"
describeTokenType T_Boludo      = "una puteada ('boludo')"
describeTokenType T_Chirimbolo  = "'chirimbolo'"
describeTokenType T_Che         = "un vocativo ('che')"
describeTokenType T_Como        = "'como'"
describeTokenType T_Con         = "'con'"
describeTokenType T_Cualidad    = "'cualidad'"
describeTokenType T_Cuyo        = "'cuyo'"
describeTokenType T_Da          = "'da'"
describeTokenType T_Dado        = "'dado'"
describeTokenType T_De          = "'dado'"
describeTokenType T_Donde       = "'donde'"
describeTokenType T_En          = "'en'"
describeTokenType T_Encarnar    = "'encarnar'"
describeTokenType T_Enchufar    = "'enchufar'"
describeTokenType T_Entregar    = "'entregar'"
describeTokenType T_Es          = "una cópula ('es', 'son')"
describeTokenType T_Gringo      = "'gringo'"
describeTokenType T_Mirar       = "'mirar'"
describeTokenType T_Para        = "'para'"
describeTokenType T_Pero        = "'pero'"
describeTokenType T_Ponele      = "'ponele'"
describeTokenType T_Que         = "'que'"
describeTokenType T_Si          = "'si'"
describeTokenType T_Tiene       = "'tiene'"
describeTokenType T_No          = "'no'"
describeTokenType T_SI          = "'SI'"
describeTokenType T_BOLUDO      = "'BOLUDO'"
describeTokenType T_LParen      = "un paréntesis '('"
describeTokenType T_RParen      = "un paréntesis ')'"
describeTokenType T_LBracket    = "un corchete '['"
describeTokenType T_RBracket    = "un corchete ']'"
describeTokenType T_LBrace      = "una llave '{'"
describeTokenType T_RBrace      = "una llave '}'"
describeTokenType T_Comma       = "una coma ','"
describeTokenType (T_Paquete p) = "el inicio del paquete " ++ showPackage p
describeTokenType T_FinPaquete  = "el final del archivo"

data Token = Token TokenType Position
  deriving Show

isIdent, isBlank :: Char -> Bool
isIdent c = isAlpha c || isDigit c || c == '_'
isBlank c = c == ' ' || c == '\t' || c == '\n' || c == '\r'
isOperator c = c `elem` [
    '!', '#', '$', '%',
    '&', '*', '+', '.',
    '/', '<', '=', '>',
    '?', '@', ':', '^',
    '|', '-', '~', '\\',
    ';', '`'
 ]

keywords :: [(Id, TokenType)]
keywords = [
    ("ante", T_Ante),
    ("bien", T_Bien),
    ("boludo", T_Boludo), ("boluda", T_Boludo),
    ("chirimbolo", T_Chirimbolo),
    ("che", T_Che),
    ("como", T_Como),
    ("con", T_Con),
    ("cualidad", T_Cualidad),
    ("cuyo", T_Cuyo), ("cuya", T_Cuyo),
                      ("cuyos", T_Cuyo),
                      ("cuyas", T_Cuyo),
    ("da", T_Da),
    ("dado", T_Dado), ("dada", T_Dado),
                      ("dados", T_Dado),
                      ("dadas", T_Dado),
    ("de", T_De),
    ("donde", T_Donde),
    ("el", T_ArticuloD), ("la", T_ArticuloD),
                         ("las", T_ArticuloD),
                         ("los", T_ArticuloD),
    ("en", T_En),
    ("encarnar", T_Encarnar),
    ("enchufar", T_Enchufar),
    ("entregar", T_Entregar),
    ("es", T_Es), ("son", T_Es),
    ("gringo", T_Gringo), ("gringa", T_Gringo),
                          ("gringos", T_Gringo),
                          ("gringas", T_Gringo),
    ("mirar", T_Mirar),
    ("no", T_No),
    ("para", T_Para),
    ("pero", T_Pero),
    ("ponele", T_Ponele),
    ("que", T_Que),
    ("si", T_Si),
    ("tiene", T_Tiene), ("tienen", T_Tiene),
    ("un", T_ArticuloI), ("una", T_ArticuloI),
                         ("unas", T_ArticuloI),
                         ("unos", T_ArticuloI)
 ]

preprocessorKeywords :: [(Id, TokenType)]
preprocessorKeywords = [
    ("SI", T_SI),
    ("BOLUDO", T_BOLUDO), ("BOLUDA", T_BOLUDO),

    ("GRINGO", T_GRINGO), ("GRINGA", T_GRINGO),
                          ("GRINGOS", T_GRINGO),
                          ("GRINGAS", T_GRINGO)
 ]

type LexerM a = StateT Position (Either String) a

runLexerM :: PackageName -> String -> LexerM a -> Either String a
runLexerM package contents m =
  evalStateT m (Position package contents 1 1)

modifyUpdatePosition :: String -> LexerM ()
modifyUpdatePosition string = modify (updatePosition string)

-- lexerFail should be defined using lift, which seems to have a bug
-- this is a workaround
lexerFail :: String -> Position -> LexerM a
lexerFail msg pos = StateT . const . Left $ (
    msg ++ "\n" ++
    "\nCerquita de: " ++ describePosition pos ++ ".\n" ++
    "----\n" ++ showNearbyCode pos ++ "\n----\n"
  )

readChar :: String -> LexerM (String, Char, String)
readChar ('\\' : 'a' : cs)  = return ("\\a", '\a', cs)
readChar ('\\' : 'b' : cs)  = return ("\\b", '\b', cs)
readChar ('\\' : 'f' : cs)  = return ("\\f", '\f', cs)
readChar ('\\' : 'n' : cs)  = return ("\\n", '\n', cs)
readChar ('\\' : 'r' : cs)  = return ("\\r", '\r', cs)
readChar ('\\' : 't' : cs)  = return ("\\t", '\t', cs)
readChar ('\\' : 'v' : cs)  = return ("\\v", '\v', cs)
readChar ('\\' : '\\' : cs) = return ("\\\\", '\\', cs)
readChar ('\\' : '\'' : cs) = return ("\\\'", '\'', cs)
readChar ('\\' : '"' : cs)  = return ("\\\"", '"', cs)
readChar (c : cs)           = return ([c], c, cs)
readChar "" = do
  pos <- get
  lexerFail (
     "Recatate.\n" ++
     "La entrada terminó antes de tiempo."
   )
   pos
-- TODO: octal, hexadecimal, unicode escapes

tokenize :: PackageName -> String -> Either String [Token]
tokenize package contents =
    runLexerM package contents (rec contents)
  where
    rec :: String -> LexerM [Token]
    rec "" = do
      pos <- get
      return [Token T_EOF pos]
    rec ('O' : 'J' : 'O' : '.' : cs) =
      -- Skip comment
      let (comment, rest) = span (/= '\n') cs in do
        modifyUpdatePosition ("OJO." ++ comment)
        rec rest
    rec ('(' : cs) = continue "(" (Token T_LParen) cs
    rec (')' : cs) = continue ")" (Token T_RParen) cs
    rec ('[' : cs) = continue "[" (Token T_LBracket) cs
    rec (']' : cs) = continue "]" (Token T_RBracket) cs
    rec ('{' : cs) = continue "{" (Token T_LBrace) cs
    rec ('}' : cs) = continue "}" (Token T_RBrace) cs
    rec (',' : cs) = continue "," (Token T_Comma) cs
    rec ('\'' : cs) = do
        (r, chr, cs') <- readChar cs
        case cs' of
          '\'' : cs'' -> continue r (Token (T_Char chr)) cs''
          _           -> do
            pos <- get
            lexerFail (
                "¿Qué onda?\n" ++
                "Esperaba otra comilla (\') para delimitar la letra."
              )
              pos
    rec ('"' : cs) = do
        (r, s, cs') <- readString cs
        continue r (Token (T_String s)) cs'
      where
        readString :: String -> LexerM (String, String, String)
        readString ('"' : cs) = return ("\"", [], cs)
        readString cs         = do
          (r1, chr, cs')  <- readChar cs
          (r2, str, cs'') <- readString cs'
          return ("\"" ++ r1 ++ r2, chr : str, cs'')
    rec (c : cs) | isBlank c = do
      modifyUpdatePosition (c : [])
      rec cs
    rec (c : cs) | isDigit c =
      let (ident, tail) = span isDigit (c : cs) in
        case tail of 
          '#' : tail' -> continue ident (Token $ T_Fixnum $ read ident) tail'
          _ -> continue ident (Token $ T_Integer $ read ident) tail

    rec cs = readId [] cs

    readId :: PackageName -> String -> LexerM [Token]
    readId package (c : cs) | isUpper c = 
      let (ident, tail) = span isIdent (c : cs)
       in case tail of
            '.' : tail' -> do
              modifyUpdatePosition (ident ++ ".")
              readId (package ++ [ident]) tail'
            _ -> case lookup ident preprocessorKeywords of
                   Just typ ->
                     continue ident (Token typ) tail
                   _        -> 
                     continue ident (Token $ T_Upperid package ident) tail
    readId package cs  = readQualified package cs

    readQualified :: PackageName -> String -> LexerM [Token]
    readQualified qualif (c : cs) | isOperator c =
      let (ident, tail) = span isOperator (c : cs)
       in continue ident (Token (T_Operator qualif ident)) tail
    readQualified qualif (c : cs) | isIdent c =
      let (ident, tail) = span isIdent (c : cs)
          tokenType = case lookup ident keywords of
                        Just typ            -> const typ
                        Nothing | isUpper c -> T_Upperid qualif
                        Nothing             -> T_Lowerid qualif
       in continue ident (Token $ tokenType ident) tail
    readQualified qualif _ = do
      pos <- get
      lexerFail (
          "Flor de error de sintaxis.\n" ++
          "El símbolo es inválido."
        )
        pos

    continue :: String -> (Position -> Token) -> String -> LexerM [Token]
    continue val token tail = do
      pos <- get
      modifyUpdatePosition val
      rest <- rec tail
      return (token pos : rest)

tokenizeOrFail :: PackageName -> String -> [Token]
tokenizeOrFail package contents =
  case tokenize package contents of
    Left msg -> error msg
    Right x  -> x

