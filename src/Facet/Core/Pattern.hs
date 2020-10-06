{-# LANGUAGE DeriveTraversable #-}
module Facet.Core.Pattern
( Pattern(..)
) where

data Pattern a
  = Wildcard
  | Var a
  | Tuple [Pattern a]
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
