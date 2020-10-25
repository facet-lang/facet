{-# LANGUAGE GADTs #-}
module Facet.Effect.Trace
( -- * Trace effect
  trace
, traceShow
, Trace(..)
) where

import Control.Algebra

trace :: Has Trace sig m => String -> m a -> m a
trace s m = send (Trace s m)

traceShow :: (Has Trace sig m, Show a) => a -> m a -> m a
traceShow = trace . show

data Trace m k where
  Trace :: String -> m a -> Trace m a
