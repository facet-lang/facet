{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Carrier.Trace.REPL
( -- * Trace carrier
  runTrace
, TraceC(TraceC)
  -- * Trace effect
, module Facet.Effect.Trace
) where

import Control.Algebra
import Control.Carrier.Reader
import Control.Monad.IO.Class
import Facet.Effect.Readline
import Facet.Effect.Trace
import Facet.Stack

runTrace :: TraceC m a -> m a
runTrace = runReader Nil . runTraceC

newtype TraceC m a = TraceC { runTraceC :: ReaderC (Stack String) m a }
  deriving (Applicative, Functor, Monad, MonadFail, MonadIO)

instance Has Readline sig m => Algebra (Trace :+: sig) (TraceC m) where
  alg hdl sig ctx = TraceC $ ReaderC $ \ stack -> case sig of
    L (Trace msg m) -> outputStrLn msg *> runReader (stack:>msg) (runTraceC (hdl (m <$ ctx)))
    L CallStack     -> pure (stack <$ ctx)
    R other         -> alg (runReader stack . runTraceC . hdl) other ctx
