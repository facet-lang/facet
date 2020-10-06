{-# LANGUAGE DeriveTraversable #-}
-- | Really just a snoc list, but the shoe fits if you squish things up just right.
module Facet.Stack
( Stack(..)
) where

data Stack a
  = Nil
  | Stack a :> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixl 5 :>
