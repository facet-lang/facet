module Facet.Carrier.Trace.REPL
( -- * Trace carrier
  runTrace
, TraceC(TraceC)
  -- * Trace effect
, module Facet.Effect.Trace
) where

import Control.Monad.IO.Class
import Facet.Effect.Trace

newtype TraceC m a = TraceC { runTrace :: m a }
  deriving (Applicative, Functor, Monad, MonadFail, MonadIO)
