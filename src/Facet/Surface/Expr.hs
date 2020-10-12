{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Surface.Expr
( Expr(..)
, unApp
) where

import Control.Effect.Empty
import Data.Text (Text)
import Facet.Name
import Facet.Surface.Comp (Clause)
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
