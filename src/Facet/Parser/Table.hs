module Facet.Parser.Table
( Assoc(..)
, Operator
, parseOperator
, OperatorParser
, Row
, Table
, build
, terminate
) where

import Control.Applicative (Alternative(..))
import Data.Foldable (foldl')
import Data.Function ((&))
import Facet.Name
import Text.Parser.Combinators
import Text.Parser.Token

type Operator a = (Op, Assoc, [a] -> a)

parseOperator :: TokenParsing p => Operator a -> OperatorParser p a
parseOperator = \case
  (Prefix   s, _, op) -> \ self _    -> unary op <$ textSymbol s <*> self
  (Postfix  s, _, op) -> \ _    next -> foldl' (&) <$> next <*> many (unary op <$ textSymbol s)
  (Infix    s, N, op) -> \ _    next -> try (binary op <$> next <* textSymbol s) <*> next
  (Infix    s, L, op) -> \ _    next -> chainl1 next (binary op <$ textSymbol s)
  (Infix    s, R, op) -> \ self next -> try (binary op <$> next <* textSymbol s) <*> self
  (Infix    s, A, op) -> \ _    next -> chainr1 next (binary op <$ textSymbol s)
  (Outfix s e, _, op) -> \ self _    -> unary op <$ textSymbol s <*> nesting self <* textSymbol e
  where
  unary f a = f [a]
  binary f a b = f [a, b]

type OperatorParser p a = p a -> p a -> p a
type Row a = [Operator a]
type Table a = [Row a]

-- | Build a parser for a Table.
build :: TokenParsing p => Table a -> p a -> p a
build ts end = root
  where
  root = foldr chain end ts
  chain ps next = self
    where
    self = foldr (\ p rest -> parseOperator p self rest <|> rest) next ps

terminate :: (p a -> p a) -> OperatorParser p a -> p a -> p a
terminate wrap op next = self where self = wrap $ op self next
