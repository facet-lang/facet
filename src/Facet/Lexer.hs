module Facet.Lexer
( Token(..)
, TokenKind(..)
) where

import Control.Applicative (Alternative(..))
import Facet.Name
import Facet.Span
import Text.Parser.Char

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
  | OpIdent String
  | MIdent MName
  | EIdent EName
  | TIdent TName


kind_ :: CharParsing p => p TokenKind
kind_ = comment
  where
  comment = Comment <$ char '#' <*> many (satisfy (/= '\n'))
