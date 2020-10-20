{-# LANGUAGE UndecidableInstances #-}
module Facet.Carrier.Throw.Inject
( -- * Throw carrier
  runThrow
, ThrowC(..)
  -- * Throw effect
, module Control.Effect.Throw
) where

import Control.Algebra
import Control.Carrier.Reader
import Control.Effect.Throw
import Control.Monad.IO.Class

runThrow :: (f -> e) -> ThrowC e f m a -> m a
runThrow inject (ThrowC m) = runReader inject m

newtype ThrowC e f m a = ThrowC (ReaderC (f -> e) m a)
  deriving (Applicative, Functor, Monad, MonadFail, MonadIO)

instance Has (Throw e) sig m => Algebra (Throw f :+: sig) (ThrowC e f m) where
  alg hdl sig ctx = ThrowC $ ReaderC $ \ inject -> case sig of
    L (Throw e) -> throwError (inject e)
    R other     -> alg (runThrow inject . hdl) other ctx
