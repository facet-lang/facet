{-# LANGUAGE GADTs #-}
module Facet.Effect.Write
( -- * Write effect
  write
, Write(..)
  -- * Re-exports
, Algebra
, Has
, run
) where

import Control.Algebra
import Data.Kind (Type)

write :: Has (Write a) sig m => a -> m ()
write = send . Write

data Write a (m :: Type -> Type) k where
  Write :: a -> Write a m ()
