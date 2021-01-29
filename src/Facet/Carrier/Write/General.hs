module Facet.Carrier.Write.General
( -- * Write carrier
  WriteC(..)
  -- * Write effect
, module Facet.Effect.Write
) where

import Control.Carrier.Reader
import Control.Monad.IO.Class (MonadIO)
import Facet.Effect.Write

newtype WriteC o m a = WriteC (ReaderC (o -> m ()) m a)
  deriving (Applicative, Functor, Monad, MonadFail, MonadIO)
