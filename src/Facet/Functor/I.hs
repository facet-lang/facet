{-# LANGUAGE DeriveTraversable #-}
module Facet.Functor.I
( I(..)
) where

import Control.Applicative (liftA2)
import Data.Coerce
import Data.Distributive

newtype I a = I { getI :: a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative I where
  pure = coerce
  {-# INLINE pure #-}

  (<*>) = coerce
  {-# INLINE (<*>) #-}

  liftA2 = coerce
  {-# INLINE liftA2 #-}

  (*>) = const id
  {-# INLINE (*>) #-}

  (<*) = const
  {-# INLINE (<*) #-}

instance Distributive I where
  distribute = I . fmap coerce
  {-# INLINE distribute #-}

  collect f = I . fmap (coerce f)
  {-# INLINE collect #-}

instance Monad I where
  a >>= f = coerce f a
  {-# INLINE (>>=) #-}

  (>>) = (*>)
  {-# INLINE (>>) #-}
