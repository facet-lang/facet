{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
module Facet.Effect.Coro
( -- * Coro effect
  Coro(..)
, yield
  -- * Re-exports
, Algebra
, Has
, run
) where

import Control.Algebra
import Data.Kind (Type)

data Coro a b (m :: Type -> Type) k where
  Yield :: a -> Coro a b m b
  -- FIXME: interception


yield :: Has (Coro a b) sig m => a -> m b
yield a = send (Yield a)
