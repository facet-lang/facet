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

instance Applicative m => Applicative (CoroC a b m) where
  pure a = CoroC $ \ _ -> pure a
  f <*> a = CoroC $ \ k -> runCoro k f <*> runCoro k a

instance Monad m => Monad (CoroC a b m) where
  a >>= f = CoroC $ \ k -> runCoro k a >>= runCoro k . f
