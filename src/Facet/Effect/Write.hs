{-# LANGUAGE GADTs #-}
module Facet.Effect.Write
( -- * Write effect
  Write(..)
  -- * Re-exports
, Algebra
, Has
, run
) where

import Control.Algebra
import Data.Kind (Type)

data Write a (m :: Type -> Type) k where
  Write :: a -> Write a m ()
