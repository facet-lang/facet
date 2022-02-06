module Facet.Functor.Synth
( -- * Synth judgement
  (:==>)(..)
  -- * Construction
, (==>)
  -- * Elimination
, proof
, prop
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


-- Construction

(==>) :: Applicative m => m (i tm) -> m ty -> m (i tm :==> ty)
tm ==> ty = (:==>) <$> tm <*> ty


-- Elimination

proof :: a :==> b -> a
proof (a :==> _) = a

prop :: a :==> b -> b
prop (_ :==> b) = b
