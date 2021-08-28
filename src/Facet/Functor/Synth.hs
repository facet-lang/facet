module Facet.Functor.Synth
( -- * Synth judgement
  (:==>)(..)
  -- * Elimination
, proof
) where

import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable

-- Synth judgement

data a :==> b = a :==> b
  deriving (Foldable, Functor, Traversable)

infixr 2 :==>

instance Bifunctor (:==>) where
  bimap = bimapDefault

instance Bifoldable (:==>) where
  bifoldMap = bifoldMapDefault

instance Bitraversable (:==>) where
  bitraverse f g (a :==> _T) = (:==>) <$> f a <*> g _T


-- Elimination

proof :: a :==> b -> a
proof (a :==> _) = a
