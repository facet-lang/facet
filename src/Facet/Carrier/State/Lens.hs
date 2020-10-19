{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Facet.Carrier.State.Lens
( -- * State carrier
  StateC(..)
) where

import Control.Carrier.Reader
import Control.Lens (ALens')

newtype StateC s t m a = StateC (ReaderC (ALens' s t) m a)
  deriving (Applicative, Functor, Monad, MonadFail)
