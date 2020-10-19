{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Facet.Carrier.State.Lens
( -- * State carrier
  StateC(..)
  -- * State effect
, module Control.Effect.State
) where

import Control.Carrier.Reader
import Control.Effect.State
import Control.Lens (ALens')

newtype StateC s t m a = StateC (ReaderC (ALens' s t) m a)
  deriving (Applicative, Functor, Monad, MonadFail)
