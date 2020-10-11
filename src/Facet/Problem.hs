-- | 'Problem's are a prefix on 'Value's, binding metavariables. Solving 'Problem's yields closed 'Value's.
module Facet.Problem
( Problem(..)
, solve
) where

import Facet.Context
import Facet.Core.Value
import Facet.Stack

data Problem f a = Exists (Context (Type f a)) (Stack (Value f a) -> f (Value f a))

solve :: Problem f a -> Stack (Value f a) -> f (Value f a)
solve (Exists _ b) a = b a
