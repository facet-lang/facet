{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Carrier.State.Lens
( -- * State carrier
  runState
, StateC(..)
  -- * State effect
, module Control.Effect.State
) where

import Control.Algebra
import Control.Carrier.Reader
import Control.Effect.State
import Control.Lens (ALens', storing, (^#))
import Control.Monad.IO.Class

runState :: ALens' s t -> StateC s t m a -> m a
runState lens (StateC m) = runReader lens m
{-# INLINE runState #-}

newtype StateC s t m a = StateC (ReaderC (ALens' s t) m a)
  deriving (Applicative, Functor, Monad, MonadFail, MonadIO)

instance Has (State s) sig m => Algebra (State t :+: sig) (StateC s t m) where
  alg hdl sig ctx = StateC $ ReaderC $ \ lens -> case sig of
    L Get     -> (<$ ctx) <$> gets (^# lens)
    L (Put s) -> (<$ ctx) <$> modify (storing lens s)
    R other   -> alg (runState lens . hdl) other ctx
  {-# INLINABLE alg #-}
