{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Carrier.Trace.REPL
( -- * Trace carrier
  runTrace
, LogTraces(..)
, TraceC(TraceC)
  -- * Trace effect
, module Facet.Effect.Trace
) where

import Control.Algebra
import Control.Carrier.Reader
import Control.Carrier.State.Church
import Control.Monad (when)
import Control.Monad.IO.Class
import Data.Semigroup (stimes)
import Facet.Effect.Readline
import Facet.Effect.Trace
import Facet.Flag
import Facet.Pretty
import Facet.Stack
import Facet.Style
import Silkscreen


runTrace :: Applicative m => Stack (Doc Style) -> Flag LogTraces -> TraceC m a -> m a
runTrace stack flag (TraceC m) = evalState flag (m stack)

data LogTraces = LogTraces

newtype TraceC m a = TraceC { runTraceC :: Stack (Doc Style) -> StateC (Flag LogTraces) m a }
  deriving (Applicative, Functor, Monad, MonadFail, MonadIO) via ReaderC (Stack (Doc Style)) (StateC (Flag LogTraces) m)

instance Has Output sig m => Algebra (Trace :+: State (Flag LogTraces) :+: sig) (TraceC m) where
  alg hdl sig ctx = TraceC $ \ stack -> case sig of
    L (Trace msg m) -> do
      logTraces <- gets (fromFlag LogTraces)
      when logTraces $ outputDocLn (stimes (length stack * 2) space <> msg)
      runTraceC (hdl (m <$ ctx)) (stack:>msg)
    L CallStack     -> pure (stack <$ ctx)
    R other         -> alg ((`runTraceC` stack) . hdl) other ctx
