-- | A lexer designed to allow us to skip whitespace, preserve comments, and produce tight spans (i.e. omitting trailing whitespace) for parsed ASTs.
module Facet.Lexer
( Token(..)
, TokenKind(..)
, token
) where

import Data.Char (isSpace)
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
  | MIdent MName
  | EIdent EName
  | TIdent TName


token :: (CharParsing p, PositionParsing p) => p Token
token = mk <$> spanned kind_ <* skipSpace
  where
  mk (s, k) = Token k s

skipSpace :: CharParsing p => p ()
skipSpace = skipMany (satisfy isSpace)

kind_ :: CharParsing p => p TokenKind
kind_ = choice
  [ Comment    <$ char '#' <*> many (satisfy (/= '\n')) <?> "line comment"
  , Underscore <$ char '_' <?> "underscore"
  , Colon      <$ char ':' <?> "colon"
  , LParen     <$ char '(' <?> "open paren"
  , RParen     <$ char ')' <?> "close paren"
  , LBrace     <$ char '{' <?> "open brace"
  , RBrace     <$ char '}' <?> "close brace"
  , LBracket   <$ char '[' <?> "open bracket"
  , RBracket   <$ char ']' <?> "close bracket"
  , LAngle     <$ char '<' <?> "open angle bracket"
  , RAngle     <$ char '>' <?> "close angle bracket"
  ]
