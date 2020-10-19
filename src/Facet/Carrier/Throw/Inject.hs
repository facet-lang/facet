{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Facet.Carrier.Throw.Inject
( -- * Throw carrier
  runThrow
, ThrowC(..)
  -- * Throw effect
, module Control.Effect.Throw
) where

import Control.Carrier.Reader
import Control.Effect.Throw

runThrow :: (f -> e) -> ThrowC e f m a -> m a
runThrow inject (ThrowC m) = runReader inject m

newtype ThrowC e f m a = ThrowC (ReaderC (f -> e) m a)
  deriving (Applicative, Functor, Monad, MonadFail)
