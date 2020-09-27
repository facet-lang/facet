{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Facet.Functor.K
( K(..)
) where

import Control.Applicative (liftA2)
import Data.Coerce
import Silkscreen
import Silkscreen.Fresh
import Silkscreen.Nesting
import Silkscreen.Precedence

newtype K a b = K { getK :: a }
  deriving (Eq, Foldable, FreshPrinter, Functor, Monoid, NestingPrinter, Num, Ord, PrecedencePrinter, Printer, Semigroup, Show, Traversable)

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
