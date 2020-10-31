module Facet.Diff
( Diff(..)
, Change
) where

import Control.Monad ((<=<))
import Facet.Surface

data Diff a b
  = MVar (Ann a)
  | Conc (Ann b)
  deriving (Functor)

type Change f a b = (f b a, f b a)
