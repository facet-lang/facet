module Facet.Carrier.Write.Inject
( -- * Write carrier
  runWrite
, WriteC(..)
  -- * Write effect
, module Facet.Effect.Write
) where

import Control.Carrier.Reader
import Control.Monad.IO.Class (MonadIO)
import Facet.Effect.Write

runWrite :: (p -> o) -> WriteC o p m a -> m a
runWrite inject (WriteC m) = runReader inject m

newtype WriteC o p m a = WriteC (ReaderC (p -> o) m a)
  deriving (Applicative, Functor, Monad, MonadFail, MonadIO)
