{-# LANGUAGE UndecidableInstances #-}
module Facet.Carrier.Trace.REPL
( -- * Trace carrier
  runTrace
, TraceC(TraceC)
  -- * Trace effect
, module Facet.Effect.Trace
) where

import Control.Algebra
import Control.Monad.IO.Class
import Facet.Effect.Readline
import Facet.Effect.Trace

newtype TraceC m a = TraceC { runTrace :: m a }
  deriving (Applicative, Functor, Monad, MonadFail, MonadIO)

instance Has Readline sig m => Algebra (Trace :+: sig) (TraceC m) where
  alg hdl sig ctx = TraceC $ case sig of
    L (Trace msg m) -> outputStrLn msg *> runTrace (hdl (m <$ ctx))
    R other         -> alg (runTrace . hdl) other ctx
