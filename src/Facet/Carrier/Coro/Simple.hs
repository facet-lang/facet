{-# LANGUAGE DeriveFunctor #-}
module Facet.Carrier.Coro.Simple
( -- * Coro carrier
  runCoro
, CoroC(..)
) where

runCoro :: (a -> m b) -> CoroC a b m k -> m k
runCoro k (CoroC m) = m k

newtype CoroC a b m k = CoroC ((a -> m b) -> m k)
  deriving (Functor)
