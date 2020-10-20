-- | A lexer designed to allow us to skip whitespace, preserve comments, and produce tight spans (i.e. omitting trailing whitespace) for parsed ASTs.
module Facet.Lexer
( Token(..)
, TokenKind(..)
, token
) where

import Data.Char (isSpace)
import Data.Coerce
import Data.Foldable (foldl')
import Data.Text (Text, pack)
import Facet.Name
import Facet.Span
import Text.Parser.Char
import Text.Parser.Combinators
import Text.Parser.Position

-- Lexer

data Token = Token
  { kind :: TokenKind
  , span :: Span
  }

data TokenKind
  = Comment String
  | Underscore
  | Colon
  | LParen
  | RParen
  | LBrace
  | RBrace
  | LBracket
  | RBracket
  | LAngle
  | RAngle
  | OpIdent String
  | QIdent QName
  | MIdent MName
  | EIdent EName
  | TIdent TName
  | HIdent UName


token :: (CharParsing p, PositionParsing p) => p Token
token = mk <$> spanned kind_ <* skipSpace
  where
  mk (s, k) = Token k s

skipSpace :: CharParsing p => p ()
skipSpace = skipMany (satisfy isSpace)

kind_ :: CharParsing p => p TokenKind
kind_ = choice
  [ Comment    <$  char '#' <*> many (satisfy (/= '\n')) <?> "line comment"
  , Underscore <$  char '_' <?> "_"
  , Colon      <$  char ':' <?> ":"
  , LParen     <$  char '(' <?> "("
  , RParen     <$  char ')' <?> ")"
  , LBrace     <$  char '{' <?> "{"
  , RBrace     <$  char '}' <?> "}"
  , LBracket   <$  char '[' <?> "["
  , RBracket   <$  char ']' <?> "]"
  , LAngle     <$  char '<' <?> "<"
  , RAngle     <$  char '>' <?> ">"
  , MIdent     <$> (foldl' (:.) . MName <$> tcomp <* dot <*> sepBy tcomp dot) <?> "module name"
  , EIdent     <$> ecomp <?> "term name"
  , TIdent     <$> tcomp <?> "type name"
  ]
  where
  dot = char '.' <?> "."
  ecomp = ident (choice [ lower, char '_' ]) nameChar
  tcomp :: (Coercible t Text, CharParsing p) => p t
  tcomp = ident (choice [ upper, char '_' ]) nameChar

ident :: (Coercible t Text, CharParsing p) => p Char -> p Char -> p t
ident i r = fmap (coerce . pack) . (:) <$> i <*> many r

nameChar :: CharParsing p => p Char
nameChar = choice [ alphaNum, char '_' ]
