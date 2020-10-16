{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Surface.Expr
( Expr(..)
, unApp
, Comp(..)
) where

import Control.Effect.Empty
import Data.List.NonEmpty
import Data.Text (Text)
import Facet.Name
import Facet.Surface.Pattern (Pattern)
import Text.Parser.Position

data Expr a
  = Free DName
  | Bound Index
  | Hole Text
  | Comp (Spanned (Comp a))
  | Spanned (Expr a) :$ Spanned (Expr a)
  | Unit
  | Spanned (Expr a) :* Spanned (Expr a)
  -- FIXME: tupling/unit should take a list of expressions
  deriving (Foldable, Functor, Show, Traversable)

infixl 9 :$
infixl 7 :*


unApp :: Has Empty sig m => Expr a -> m (Spanned (Expr a), Spanned (Expr a))
unApp = \case
  f :$ a -> pure (f, a)
  _      -> empty


data Comp a
  = Expr (Spanned (Expr a))
  | Clauses [(NonEmpty (Spanned (Pattern UName)), Spanned (Expr a))]
  deriving (Foldable, Functor, Show, Traversable)
