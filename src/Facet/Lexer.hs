module Facet.Lexer
( Token(..)
, TokenKind(..)
) where

import Facet.Name
import Facet.Span

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
