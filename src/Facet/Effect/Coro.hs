{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
module Facet.Effect.Coro
( Coro(..)
) where

import Data.Kind (Type)

data Coro a b (m :: Type -> Type) k where
  Yield :: a -> Coro a b m b
