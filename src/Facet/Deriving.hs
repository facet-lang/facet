{-# LANGUAGE ScopedTypeVariables #-}
module Facet.Deriving
( MonadInstance(..)
) where

import Control.Monad (ap, liftM)

newtype MonadInstance m a = MonadInstance (m a)

instance Monad m => Functor (MonadInstance m) where
  fmap f (MonadInstance m) = MonadInstance (liftM f m)
  {-# INLINE fmap #-}

  a <$ MonadInstance m = MonadInstance (liftM (const a) m)
  {-# INLINE (<$) #-}

instance Monad m => Applicative (MonadInstance m) where
  pure = MonadInstance . return
  {-# INLINE pure #-}
  MonadInstance f <*> MonadInstance a = MonadInstance (ap f a)
  {-# INLINE (<*>) #-}
