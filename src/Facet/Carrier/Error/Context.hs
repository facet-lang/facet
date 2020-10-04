{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Carrier.Error.Context
( runError
, ErrorC(..)
  -- * Re-exports
, module Control.Effect.Error
) where

import           Control.Algebra
import qualified Control.Carrier.Error.Church as E
import           Control.Effect.Error
import           Control.Effect.Reader (Reader, ask)
import           Control.Monad.Fix (MonadFix)

runError :: (c -> e -> m b) -> (a -> m b) -> ErrorC c e m a -> m b
runError e p = E.runError (uncurry e) p . runErrorC

newtype ErrorC c e m a = ErrorC { runErrorC :: E.ErrorC (c, e) m a }
  deriving (Applicative, Functor, Monad, MonadFix)

instance Has (Reader c) sig m => Algebra (Error e :+: sig) (ErrorC c e m) where
  alg hdl sig ctx = ErrorC $ case sig of
    L (L (Throw e))   -> ask @c >>= throwError . flip (,) e
    L (R (Catch m h)) -> runErrorC (hdl (m <$ ctx)) `catchError` (runErrorC . hdl . (<$ ctx) . h . snd @c)
    R other           -> alg (runErrorC . hdl) (R other) ctx
