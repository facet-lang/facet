{-# LANGUAGE DeriveTraversable #-}
-- | Really just a snoc list, but the shoe fits if you squish things up just right.
module Facet.Stack
( Stack(..)
, fromList
) where

import Data.Foldable (foldl')

data Stack a
  = Nil
  | Stack a :> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixl 5 :>

instance Semigroup (Stack a) where
  a <> Nil       = a
  a <> (bs :> b) = (a <> bs) :> b

instance Monoid (Stack a) where
  mempty = Nil


fromList :: [a] -> Stack a
fromList = foldl' (:>) Nil
