module Facet.Carrier.Trace.REPL
( -- * Trace carrier
  runTrace
, TraceC(TraceC)
  -- * Trace effect
, module Facet.Effect.Trace
) where

import Facet.Effect.Trace

newtype TraceC m a = TraceC { runTrace :: m a }
