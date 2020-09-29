{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Carrier.Error.Span
( runError
, ErrorC(..)
  -- * Re-exports
, module Control.Effect.Error
) where

import           Control.Algebra
import qualified Control.Carrier.Error.Church as E
import           Control.Effect.Error
import           Control.Effect.Reader (Reader, ask)
import           Control.Effect.Parser.Span
import           Control.Monad.Fix (MonadFix)

runError :: Applicative m => ErrorC e m a -> m (Either (Span, e) a)
runError = E.runError (pure . Left) (pure . Right) . runErrorC

newtype ErrorC e m a = ErrorC { runErrorC :: E.ErrorC (Span, e) m a }
  deriving (Applicative, Functor, Monad, MonadFix)

instance Has (Reader Span) sig m => Algebra (Error e :+: sig) (ErrorC e m) where
  alg hdl sig ctx = ErrorC $ case sig of
    L (L (Throw e))   -> ask @Span >>= throwError . flip (,) e
    L (R (Catch m h)) -> runErrorC (hdl (m <$ ctx)) `catchError` (runErrorC . hdl . (<$ ctx) . h . snd @Span)
    R other           -> alg (runErrorC . hdl) (R other) ctx
