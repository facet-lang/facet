module Facet.Carrier.Error.Catch
( -- * Catch Carrier
  ErrorC(..)
  -- * Catch effect
, module Control.Effect.Catch
) where

import Control.Effect.Catch

newtype ErrorC e m a = ErrorC { runError :: m a }
