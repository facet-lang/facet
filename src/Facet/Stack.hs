{-# LANGUAGE DeriveTraversable #-}
-- | Really just a snoc list, but the shoe fits if you squish things up just right.
module Facet.Stack
( Stack(..)
, fromList
, (!)
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


(!) :: Stack a -> Int -> a
as' ! i' = go as' i'
  where
  go (as :> a) i
    | i <= 0     = a
    | otherwise  = go as (i - 1)
  go _         _ = error $ "Facet.Stack.!: index (" <> show i' <> ") out of bounds (" <> show (length as') <> ")"
