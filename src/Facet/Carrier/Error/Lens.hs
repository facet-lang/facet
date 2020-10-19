{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Facet.Carrier.Error.Lens
( -- * Error carrier
  runError
, ErrorC(..)
) where

import Control.Carrier.Reader
import Control.Lens (APrism')

runError :: APrism' e f -> ErrorC e f m a -> m a
runError prism (ErrorC m) = runReader prism m

newtype ErrorC e f m a = ErrorC (ReaderC (APrism' e f) m a)
  deriving (Applicative, Functor, Monad, MonadFail)
