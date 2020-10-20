{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Carrier.Error.Lens
( -- * Error carrier
  runError
, ErrorC(..)
  -- * Error effect
, module Control.Effect.Error
) where

import Control.Algebra
import Control.Carrier.Reader
import Control.Effect.Error
import Control.Lens (APrism', withPrism)
import Control.Monad.IO.Class

runError :: APrism' e f -> ErrorC e f m a -> m a
runError prism (ErrorC m) = runReader prism m

newtype ErrorC e f m a = ErrorC (ReaderC (APrism' e f) m a)
  deriving (Applicative, Functor, Monad, MonadFail, MonadIO)

instance Has (Error e) sig m => Algebra (Error f :+: sig) (ErrorC e f m) where
  alg hdl sig ctx = ErrorC $ ReaderC $ \ prism -> case sig of
    L (L (Throw e))   -> throwError (withPrism prism (\ review _ -> review e))
    L (R (Catch m h)) -> runError prism (hdl (m <$ ctx)) `catchError` \ e -> withPrism prism (\ _ preview -> either throwError (runError prism . hdl . (<$ ctx) . h) (preview e))
    R other           -> alg (runError prism . hdl) other ctx
