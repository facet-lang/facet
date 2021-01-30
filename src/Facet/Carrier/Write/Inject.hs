{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Carrier.Write.Inject
( -- * Write carrier
  runWrite
, WriteC(..)
  -- * Write effect
, module Facet.Effect.Write
) where

import Control.Algebra
import Control.Carrier.Reader
import Control.Monad.IO.Class (MonadIO)
import Facet.Effect.Write

runWrite :: (p -> o) -> WriteC o p m a -> m a
runWrite inject (WriteC m) = runReader inject m

newtype WriteC o p m a = WriteC (ReaderC (p -> o) m a)
  deriving (Applicative, Functor, Monad, MonadFail, MonadIO)

instance Has (Write o) sig m => Algebra (Write p :+: sig) (WriteC o p m) where
  alg hdl sig ctx = WriteC $ ReaderC $ \ inject -> case sig of
    L (Write o) -> ctx <$ write (inject o)
    R other     -> alg (runWrite inject . hdl) other ctx
