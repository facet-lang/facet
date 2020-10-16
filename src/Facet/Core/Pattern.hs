{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Core.Pattern
( Pattern(..)
) where

-- FIXME: represent wildcard patterns as var patterns with an empty name.
data Pattern a
  = Wildcard
  | Var a
  | Tuple [Pattern a]
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
