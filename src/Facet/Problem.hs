{-# LANGUAGE TypeOperators #-}
-- | 'Problem's are a prefix on 'Value's, binding metavariables. Solving 'Problem's yields closed 'Value's.
module Facet.Problem
( Problem(..)
, solve
, solves
) where

import Data.Foldable (foldl')
import Facet.Core.Value
import Facet.Name
import Facet.Syntax
import GHC.Stack

data Problem f a
  = Exists (UName ::: Type f a) (Value f a -> f (Problem f a))
  | Body (Value f a)

solve :: HasCallStack => Problem f a -> Value f a -> f (Problem f a)
solve (Exists _ b) a = b a
solve _            _ = error "can’t solve non-existential problem"

solves :: (HasCallStack, Foldable t, Monad f) => Problem f a -> t (Value f a) -> f (Problem f a)
solves f as = foldl' (\ f a -> f >>= (`solve` a)) (pure f) as
