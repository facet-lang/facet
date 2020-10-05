{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
module Facet.Parser.Table
( BindCtx(..)
, Assoc(..)
, Operator(..)
, toBindParser
, BindParser
, Table
, build
, terminate
) where

import Control.Applicative (Alternative(..), (<**>))
import Text.Parser.Combinators
import Text.Parser.Position

data BindCtx p a = BindCtx
  { self :: p a
  , next :: p a
  }

data Assoc = N | L | R

data Operator p a
  -- TODO: prefix, postfix, mixfix
  = Infix Assoc (p (a -> a -> a))
  | Binder (BindParser p a)
  | Atom (p a)

toBindParser :: (PositionParsing p, Spanned a) => Operator p a -> BindParser p a
toBindParser = \case
  Infix N op -> \ BindCtx{ next } -> try (next <**> op) <*> next
  Infix L op -> \ BindCtx{ next } -> chainl1Loc next op
  Infix R op -> \ BindCtx{ self, next } -> try (next <**> op) <*> self
  Binder p   -> p
  Atom p     -> const p
  where

type BindParser p a = BindCtx p a -> p a
type Table p a = [[Operator p a]]

-- | Build a parser for a Table.
build :: (PositionParsing p, Spanned a) => Table p a -> (p a -> p a) -> p a
build ts end = root
  where
  root = foldr chain (end root) ts
  chain ps next = self
    where
    self = foldr (\ p rest -> toBindParser p BindCtx{ self, next } <|> rest) next ps

terminate :: (p a -> p a) -> BindParser p a -> p a -> p a
terminate wrap op next = self where self = wrap $ op BindCtx{ next, self }
