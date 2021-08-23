module Facet.Functor.Synth
( -- * Synth judgement
  Synth(..)
) where

import Facet.Type.Norm

-- Synth judgement

data Synth a = a :==> Type
  deriving (Foldable, Functor, Traversable)

infixr 2 :==>
