{-# LANGUAGE GADTs #-}
module Facet.Effect.Trace
( -- * Trace effect
  Trace(..)
) where

data Trace m k where
  Trace :: String -> m a -> Trace m a
