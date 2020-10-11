{-# LANGUAGE TypeOperators #-}
-- | 'Problem's are a prefix on 'Value's, binding metavariables. Solving 'Problem's yields closed 'Value's.
module Facet.Problem
( Problem(..)
) where

import Facet.Core.Value
import Facet.Name
import Facet.Syntax

data Problem f a
  = Exists (UName ::: Type f a) (Value f a -> f (Problem f a))
  | Body (Value f a)
