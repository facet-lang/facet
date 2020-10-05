{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Surface.Pattern
( Pattern(..)
) where

import Text.Parser.Position (Span, Spanned(..))

data Pattern a
  = Wildcard
  | Var a
  | Tuple [Pattern a]
  | Loc Span (Pattern a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Spanned (Pattern a) where
  setSpan = Loc

  dropSpan = \case
    Loc _ d -> dropSpan d
    d       -> d
