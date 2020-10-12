-- | 'Problem's are a prefix on 'Value's, binding metavariables. Solving 'Problem's yields closed 'Value's.
module Facet.Problem
( Problem(..)
) where

import Facet.Context
import Facet.Core.Value
import Facet.Stack

data Problem f a = Exists
  { metas :: Context (Value f a)
  , solve :: Stack (Value f a) -> f (Value f a)
  }
