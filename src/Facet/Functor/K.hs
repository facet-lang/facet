{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Facet.Functor.K
( K(..)
) where

import Control.Applicative (liftA2)
import Data.Coerce

newtype K a b = K { getK :: a }
  deriving (Eq, Foldable, Functor, Monoid, Num, Ord, Semigroup, Show, Traversable)

instance Monoid a => Applicative (K a) where
  pure _ = K mempty
  {-# INLINE pure #-}

  (<*>) = coerce ((<>) :: a -> a -> a)
  {-# INLINE (<*>) #-}

  liftA2 _ = coerce ((<>) :: a -> a -> a)
  {-# INLINE liftA2 #-}

  (*>) = coerce ((<>) :: a -> a -> a)
  {-# INLINE (*>) #-}

  (<*) = coerce ((<>) :: a -> a -> a)
  {-# INLINE (<*) #-}
