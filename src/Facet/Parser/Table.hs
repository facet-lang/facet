module Facet.Parser.Table
( Assoc(..)
, Operator
, parseOperator
, atom
, OperatorParser
, Row
, Table
, build
, buildRow
) where

import Control.Applicative (Alternative(..), (<**>))
import Data.Function ((&))
import Facet.Name
import Text.Parser.Combinators
import Text.Parser.Token

type Operator a = (Op, Assoc, [a] -> a)

parseOperator :: TokenParsing p => Operator a -> OperatorParser p a
parseOperator = \case
  (Prefix   s, _, op) -> \ self next -> unary op <$ textSymbol s <*> self <|> next
  (Postfix  s, _, op) -> \ _    next -> foldl' (&) <$> next <*> many (unary op <$ textSymbol s)
  (Infix    s, N, op) -> \ _    next -> next <**> (flip (binary op) <$ textSymbol s <*> next <|> pure id)
  (Infix    s, L, op) -> \ _    next -> chainl1 next (binary op <$ textSymbol s)
  (Infix    s, R, op) -> \ self next -> next <**> (flip (binary op) <$ textSymbol s <*> self <|> pure id)
  (Infix    s, A, op) -> \ _    next -> chainr1 next (binary op <$ textSymbol s)
  (Outfix s e, _, op) -> \ self next -> unary op <$ textSymbol s <*> nesting self <* textSymbol e <|> next
  where
  unary f a = f [a]
  binary f a b = f [a, b]

atom :: Alternative p => p a -> OperatorParser p a
atom p _ next = p <|> next

type OperatorParser p a = p a -> p a -> p a
type Row p a = [OperatorParser p a]
type Table p a = [Row p a]

-- | Build a parser for a Table.
build :: Table p a -> p a -> p a
build rs end = foldr buildRow end rs

buildRow :: Row p a -> p a -> p a
buildRow ps next = let self = foldr (\ p -> p self) next ps in self
