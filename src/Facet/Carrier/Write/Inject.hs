module Facet.Carrier.Write.Inject
( -- * Write carrier
  WriteC(..)
  -- * Write effect
, module Facet.Effect.Write
) where

import Control.Carrier.Reader
import Control.Monad.IO.Class (MonadIO)
import Facet.Effect.Write

newtype WriteC o p m a = WriteC (ReaderC (p -> o) m a)
  deriving (Applicative, Functor, Monad, MonadFail, MonadIO)
