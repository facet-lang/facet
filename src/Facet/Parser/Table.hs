{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
module Facet.Parser.Table
( Assoc(..)
, Operator(..)
, toBindParser
, OperatorParser
, Table
, build
, terminate
) where

import Control.Applicative (Alternative(..), (<**>))
import Text.Parser.Combinators
import Text.Parser.Position

data Assoc = N | L | R

data Operator p a
  -- TODO: prefix, postfix, mixfix
  = Infix Assoc (p (a -> a -> a))
  | Binder (OperatorParser p a)
  | Atom (p a)

toBindParser :: (PositionParsing p, Spanned a) => Operator p a -> OperatorParser p a
toBindParser = \case
  Infix N op -> \ _ next -> try (next <**> op) <*> next
  Infix L op -> \ _ next -> chainl1Loc next op
  Infix R op -> \ self next -> try (next <**> op) <*> self
  Binder p   -> p
  Atom p     -> const (const p)
  where

type OperatorParser p a = p a -> p a -> p a
type Table p a = [[Operator p a]]

-- | Build a parser for a Table.
build :: (PositionParsing p, Spanned a) => Table p a -> (p a -> p a) -> p a
build ts end = root
  where
  root = foldr chain (end root) ts
  chain ps next = self
    where
    self = foldr (\ p rest -> toBindParser p self next <|> rest) next ps

terminate :: (p a -> p a) -> OperatorParser p a -> p a -> p a
terminate wrap op next = self where self = wrap $ op self next
