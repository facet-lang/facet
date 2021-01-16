module Data.Semialign.Exts
( zipWithM
) where

import Data.Semialign as S

zipWithM :: (Applicative m, Traversable t, Zip t) => (a -> b -> m c) -> t a -> t b -> m (t c)
zipWithM f xs ys = sequenceA $ S.zipWith f xs ys
