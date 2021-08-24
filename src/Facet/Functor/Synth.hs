module Facet.Functor.Synth
( -- * Synth judgement
  (:==>)(..)
) where

import Data.Bifunctor

-- Synth judgement

data a :==> b = a :==> b
  deriving (Foldable, Functor, Traversable)

infixr 2 :==>

instance Bifunctor (:==>) where
  bimap f g (a :==> _T) = f a :==> g _T
