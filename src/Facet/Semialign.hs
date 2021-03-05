module Facet.Semialign
( zipWithM
, zipWithM_
, module S
) where

import Data.Foldable (sequenceA_)
import Data.Semialign as S

zipWithM :: (Applicative m, Traversable t, Zip t) => (a -> b -> m c) -> t a -> t b -> m (t c)
zipWithM f xs ys = sequenceA $ S.zipWith f xs ys

zipWithM_ :: (Applicative m, Foldable t, Zip t) => (a -> b -> m c) -> t a -> t b -> m ()
zipWithM_ f xs ys = sequenceA_ $ S.zipWith f xs ys
