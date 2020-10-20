-- | A lexer designed to allow us to skip whitespace, preserve comments, and produce tight spans (i.e. omitting trailing whitespace) for parsed ASTs.
module Facet.Lexer
( Token(..)
, TokenKind(..)
, token
) where

import Control.Applicative ((<|>))
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
kind_ = comment <|> underscore <|> colon <|> lparen <|> rparen <|> lbrace <|> rbrace
  where
  comment = Comment <$ char '#' <*> many (satisfy (/= '\n'))
  underscore = Underscore <$ char '_'
  colon = Colon <$ char ':'
  lparen = LParen <$ char '('
  rparen = RParen <$ char ')'
  lbrace = LBrace <$ char '{'
  rbrace = RBrace <$ char '}'
