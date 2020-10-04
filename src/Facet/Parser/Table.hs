{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
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
, chainl1_
) where

import Control.Applicative (Alternative(..), (<**>))
import Text.Parser.Combinators

data BindCtx p a b = BindCtx
  { self :: p a -> p b
  , next :: p a -> p b
  , vars :: p a
  }

data ExprCtx p a = ExprCtx
  { self :: p a
  , next :: p a
  }

toExprCtx :: BindCtx p a b -> ExprCtx p b
toExprCtx BindCtx{ self, next, vars } = ExprCtx{ self = self vars, next = next vars }

data Assoc = N | L | R

data Operator p a b
  -- TODO: prefix, postfix, mixfix
  = Infix Assoc (p b -> p b) (p (b -> b -> b))
  | Binder (BindParser p a b)
  | Atom (p a -> p b)

toBindParser :: Parsing p => Operator p a b -> BindParser p a b
toBindParser = \case
  Infix N wrap op -> (\ ExprCtx{ next } -> wrap (try (next <**> op) <*> next)) . toExprCtx
  Infix L wrap op -> (\ ExprCtx{ next } -> chainl1_ next wrap op) . toExprCtx
  Infix R wrap op -> (\ ExprCtx{ self, next } -> wrap (try (next <**> op) <*> self)) . toExprCtx
  Binder p        -> p
  Atom p          -> p . vars

type BindParser p a b = BindCtx p a b -> p b
type Table p a b = [[Operator p a b]]

-- | Build a parser for a Table.
build :: Parsing p => Table p a b -> ((p a -> p b) -> (p a -> p b)) -> (p a -> p b)
build ts end = root
  where
  root = foldr chain (end root) ts
  chain ps next = self
    where
    self = foldr (\ p rest vars -> toBindParser p BindCtx{ self, next, vars } <|> rest vars) next ps

terminate :: (p b -> p b) -> BindParser p a b -> (p a -> p b) -> (p a -> p b)
terminate wrap op next = self where self vars = wrap $ op BindCtx{ next, self, vars }


chainl1_ :: Alternative m => m a -> (m a -> m a) -> m (a -> a -> a) -> m a
chainl1_ p wrap op = go where go = wrap $ p <**> (flip <$> op <*> go <|> pure id)
