{-# LANGUAGE GADTs #-}
module Facet.Effect.Trace
( -- * Trace effect
  trace
, traceShow
, callStack
, Trace(..)
  -- * Re-exports
, Algebra
, Has
, run
) where

import Control.Algebra
import Facet.Stack

trace :: Has Trace sig m => String -> m a -> m a
trace s m = send (Trace s m)

traceShow :: (Has Trace sig m, Show b) => b -> m a -> m a
traceShow = trace . show

-- FIXME: Text, probably
callStack :: Has Trace sig m => m (Stack String)
callStack = send CallStack

data Trace m k where
  Trace :: String -> m a -> Trace m a
  CallStack :: Trace m (Stack String)
