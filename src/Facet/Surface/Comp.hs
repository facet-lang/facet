{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Surface.Comp
( Clause(..)
, unClause
, mapComp
) where

import Control.Effect.Empty
import Facet.Name
import Facet.Surface.Pattern (Pattern)
import Text.Parser.Position (Span, Spanned(..))

data Clause f a
  = Clause (Pattern UName) (Clause f a)
  | Body (f a)
  | Loc Span (Clause f a)
  deriving (Foldable, Functor, Show, Traversable)

instance Spanned (Clause f Span) where
  setSpan = Loc

  dropSpan = \case
    Loc _ d -> dropSpan d
    d       -> d


unClause :: Has Empty sig m => Clause f a -> m (Pattern UName, Clause f a)
unClause = \case{ Clause p c -> pure (p, c) ; _ -> empty }


mapComp :: (f a -> g b) -> Clause f a -> Clause g b
mapComp f = go
  where
  go = \case
    Clause p c -> Clause p (go c)
    Body e     -> Body (f e)
    Loc s c    -> Loc s (go c)
