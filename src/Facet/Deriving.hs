module Facet.Deriving
( ApplicativeInstance(..)
, MonadInstance(..)
) where

import Control.Applicative (liftA, liftA2)
import Control.Monad (ap, liftM, liftM2)

-- | 'Functor' instances derivable via an 'Applicative' instance, for use with @-XDerivingVia@.
--
-- Define an 'Applicative' instance for your type @A@, and then add @deriving ('Functor') via 'ApplicativeInstance' A@. E.g.:
--
-- @
-- data Validation e a = Failure e | Success a
--   deriving (Functor) via ApplicativeInstance (Validation e)
--
-- instance Semigroup e => Applicative (Validation e) where
--   pure = Success
--   Failure a <*> Failure b = Failure (a <> b)
--   Failure a <*> _         = Failure a
--   _         <*> Failure b = Failure b
--   Success f <*> Success a = Success (f a)
-- @
--
-- NB:
--
-- 1. There is no 'Applicative' instance defined for 'ApplicativeInstance' itself to avoid accidentally deriving confusing circular definitions.
-- 2. If you are able to define a 'Monad' instance for your type, you may wish to consider using 'MonadInstance' instead.
newtype ApplicativeInstance m a = ApplicativeInstance (m a)

instance Applicative m => Functor (ApplicativeInstance m) where
  fmap f (ApplicativeInstance m) = ApplicativeInstance (liftA f m)
  {-# INLINE fmap #-}

  a <$ ApplicativeInstance m = ApplicativeInstance (liftA (const a) m)
  {-# INLINE (<$) #-}


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

  MonadInstance ma <* MonadInstance mb = MonadInstance $ do { a <- ma ; _ <- mb ; return a }
  {-# INLINE (<*) #-}
