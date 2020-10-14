module Facet.Carrier.Coro.Simple
( -- * Coro carrier
  CoroC(..)
) where

newtype CoroC a b m k = CoroC ((a -> m b) -> m k)
