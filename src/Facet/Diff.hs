module Facet.Diff
( Diff(..)
, Change
) where

import Facet.Surface

data Diff a b
  = Hole (Ann a)
  | Ann (Ann b)

type Change f a = (f a, f a)
