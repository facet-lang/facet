{-# LANGUAGE GADTs #-}
module Facet.Effect.Trace
( -- * Trace effect
  trace
, Trace(..)
) where

import Control.Algebra

trace :: Has Trace sig m => String -> m a -> m a
trace s m = send (Trace s m)

data Trace m k where
  Trace :: String -> m a -> Trace m a
