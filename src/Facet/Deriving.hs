{-# LANGUAGE ScopedTypeVariables #-}
module Facet.Deriving
( MonadInstance(..)
) where

import Control.Applicative (liftA2)
import Control.Monad (ap, liftM, liftM2)

-- | 'Functor' & 'Applicative' instances derivable via a 'Monad' instance, for use with @-XDerivingVia@.
--
-- Define a 'Monad' instance for your type @M@, and then add @deriving ('Functor', 'Applicative') via 'MonadInstance' M@. E.g.:
--
-- @
-- data Opt a = None | Some a
--   deriving (Functor, Applicative) via MonadInstance Opt
--
-- instance Monad Opt where
--   return = Some
--   None   >>= _ = None
--   Some a >>= f = f a
-- @
--
-- NB:
--
-- 1. There is no 'Monad' instance defined for 'MonadInstance' itself to avoid accidentally deriving confusing circular definitions.
-- 2. Your 'Monad' instance /must/ define 'return'. This will trigger @-Wnoncanonical-monad-instances@ if that is enabled, so you may wish to disable that warning local to the module with an @OPTIONS_GHC -Wno-noncanonical-monad-instances@ pragma.
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

  liftA2 f (MonadInstance ma) (MonadInstance mb) = MonadInstance $ liftM2 f ma mb
  {-# INLINE liftA2 #-}

  MonadInstance ma *> MonadInstance mb = MonadInstance $ ma >> mb
  {-# INLINE (*>) #-}
