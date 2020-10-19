{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Facet.Carrier.Throw.Inject
( -- * Throw carrier
  runThrow
, ThrowC(..)
) where

import Control.Carrier.Reader

runThrow :: (f -> e) -> ThrowC e f m a -> m a
runThrow inject (ThrowC m) = runReader inject m

newtype ThrowC e f m a = ThrowC (ReaderC (f -> e) m a)
  deriving (Applicative, Functor, Monad, MonadFail)
