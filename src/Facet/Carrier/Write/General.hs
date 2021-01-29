module Facet.Carrier.Write.General
( -- * Write carrier
  runWrite
, WriteC(..)
  -- * Write effect
, module Facet.Effect.Write
) where

import Control.Carrier.Reader
import Control.Monad.IO.Class (MonadIO)
import Facet.Effect.Write

runWrite :: (o -> m ()) -> WriteC o m a -> m a
runWrite handle (WriteC m) = runReader handle m

newtype WriteC o m a = WriteC (ReaderC (o -> m ()) m a)
  deriving (Applicative, Functor, Monad, MonadFail, MonadIO)
