module Facet.Diff
( Diff(..)
) where

import Facet.Surface

data Diff a b
  = Hole (Ann a)
  | Ann (Ann b)
