{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Facet.Carrier.State.Lens
( -- * State carrier
  runState
, StateC(..)
  -- * State effect
, module Control.Effect.State
) where

import Control.Carrier.Reader
import Control.Effect.State
import Control.Lens (ALens')

runState :: ALens' s t -> StateC s t m a -> m a
runState lens (StateC m) = runReader lens m

newtype StateC s t m a = StateC (ReaderC (ALens' s t) m a)
  deriving (Applicative, Functor, Monad, MonadFail)
