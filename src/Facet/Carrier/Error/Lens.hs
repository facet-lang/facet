{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Facet.Carrier.Error.Lens
( -- * Error carrier
  ErrorC(..)
) where

import Control.Carrier.Reader
import Control.Lens (APrism')

newtype ErrorC e f m a = ErrorC (ReaderC (APrism' e f) m a)
  deriving (Applicative, Functor, Monad, MonadFail)
