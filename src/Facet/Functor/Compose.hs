module Facet.Functor.Compose
( -- * Composition functor
  type (.)(..)
) where

-- Composition functor

newtype (i . j) a = C { runC :: i (j a) }
  deriving (Functor)
