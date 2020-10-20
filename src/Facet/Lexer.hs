module Facet.Lexer
( Token(..)
, TokenKind(..)
, token
) where

import Control.Applicative (Alternative(..))
import Facet.Name
import Facet.Span
import Text.Parser.Char
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
  | OpIdent String
  | MIdent MName
  | EIdent EName
  | TIdent TName


token :: (CharParsing p, PositionParsing p) => p Token
token = mk <$> spanned kind_
  where
  mk (s, k) = Token k s

kind_ :: CharParsing p => p TokenKind
kind_ = comment
  where
  comment = Comment <$ char '#' <*> many (satisfy (/= '\n'))
