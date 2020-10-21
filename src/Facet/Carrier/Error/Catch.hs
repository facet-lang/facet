module Facet.Carrier.Error.Catch
( -- * Catch Carrier
  ErrorC(..)
  -- * Catch effect
, module Control.Effect.Catch
) where

import Control.Effect.Catch
import Control.Monad.IO.Class

newtype ErrorC e m a = ErrorC { runError :: m a }
  deriving (Applicative, Functor, Monad, MonadFail, MonadIO)
