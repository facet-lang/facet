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
  [ Comment <$ char '#' <*> many (satisfy (/= '\n'))
  , Underscore <$ char '_'
  , Colon <$ char ':'
  , LParen <$ char '('
  , RParen <$ char ')'
  , LBrace <$ char '{'
  , RBrace <$ char '}'
  , LBracket <$ char '['
  , RBracket <$ char ']'
  , LAngle <$ char '<'
  , RAngle <$ char '>'
  ]
