{-# LANGUAGE ScopedTypeVariables #-}
module Facet.Deriving
( MonadInstance(..)
) where

import Control.Monad (liftM)

newtype MonadInstance m a = MonadInstance (m a)

instance Monad m => Functor (MonadInstance m) where
  fmap f (MonadInstance m) = MonadInstance (liftM f m)
  {-# INLINE fmap #-}
