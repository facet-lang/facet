{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Surface.Expr
( Expr(..)
, unApp
, Clause(..)
, unClause
, mapComp
) where

import Control.Effect.Empty
import Data.Text (Text)
import Facet.Name
import Facet.Surface.Pattern (Pattern)
import Prelude hiding ((**))
import Text.Parser.Position (Span, Spanned(..))

data Expr a
  = Free DName
  | Bound Index
  | Hole Text
  | Comp [Clause Expr a]
  | Expr a :$ Expr a
  | Unit
  | Expr a :* Expr a
  | Loc a (Expr a)
  deriving (Foldable, Functor, Show, Traversable)
  -- FIXME: tupling/unit should take a list of expressions

infixl 9 :$
infixl 7 :*

instance Spanned (Expr Span) where
  setSpan = Loc

  dropSpan = \case
    Loc _ d -> dropSpan d
    d       -> d


unApp :: Has Empty sig m => Expr a -> m (Expr a, Expr a)
unApp = \case
  f :$ a -> pure (f, a)
  _      -> empty


data Clause f a
  = Clause (Pattern UName) (Clause f a)
  | Body (f a)
  | CLoc Span (Clause f a)
  deriving (Foldable, Functor, Show, Traversable)

instance Spanned (Clause f Span) where
  setSpan = CLoc

  dropSpan = \case
    CLoc _ d -> dropSpan d
    d        -> d


unClause :: Has Empty sig m => Clause f a -> m (Pattern UName, Clause f a)
unClause = \case{ Clause p c -> pure (p, c) ; _ -> empty }


mapComp :: (f a -> g b) -> Clause f a -> Clause g b
mapComp f = go
  where
  go = \case
    Clause p c -> Clause p (go c)
    Body e     -> Body (f e)
    CLoc s c   -> CLoc s (go c)
