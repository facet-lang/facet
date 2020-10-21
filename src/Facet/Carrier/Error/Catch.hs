module Facet.Carrier.Error.Catch
( -- * Error Carrier
  ErrorC(..)
  -- * Error effect
, module Control.Effect.Error
) where

import Control.Effect.Error
import Control.Monad.IO.Class

newtype ErrorC e m a = ErrorC { runError :: m a }
  deriving (Applicative, Functor, Monad, MonadFail, MonadIO)
