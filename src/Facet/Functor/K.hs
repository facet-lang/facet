{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Facet.Functor.K
( K(..)
) where

newtype K a b = K { getK :: a }
  deriving (Eq, Foldable, Functor, Num, Ord, Show, Traversable)
