module Facet.Functor.Synth
( -- * Synth judgement
  (:==>)(..)
) where

-- Synth judgement

data a :==> b = a :==> b
  deriving (Foldable, Functor, Traversable)

infixr 2 :==>
