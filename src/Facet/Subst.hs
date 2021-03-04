{-# LANGUAGE FunctionalDependencies #-}
module Facet.Subst
( -- * Substitutions
  Subst(..)
, insert
, lookupMeta
, solveMeta
, declareMeta
, metas
  -- * Applying substitutions
, Substitutable(..)
) where

import qualified Data.IntMap as IntMap
import           Facet.Name
import           Facet.Syntax

newtype Subst v t = Subst (IntMap.IntMap (Maybe v ::: t))
  deriving (Monoid, Semigroup)

insert :: Meta -> Maybe v ::: t -> Subst v t -> Subst v t
insert (Meta i) t (Subst metas) = Subst (IntMap.insert i t metas)

lookupMeta :: Meta -> Subst v t -> Maybe (v ::: t)
lookupMeta (Meta i) (Subst metas) = do
  v ::: _T <- IntMap.lookup i metas
  (::: _T) <$> v

solveMeta :: Meta -> v -> Subst v t -> Subst v t
solveMeta (Meta i) t (Subst metas) = Subst (IntMap.update (\ (_ ::: _T) -> Just (Just t ::: _T)) i metas)

declareMeta :: t -> Subst v t -> (Subst v t, Meta)
declareMeta _K (Subst metas) = (Subst (IntMap.insert v (Nothing ::: _K) metas), Meta v) where
  v = maybe 0 (succ . fst . fst) (IntMap.maxViewWithKey metas)

metas :: Subst v t -> [Meta :=: Maybe v ::: t]
metas (Subst metas) = map (\ (k, v) -> Meta k :=: v) (IntMap.toList metas)


class Substitutable a v t | a -> v t where
  (|->) :: Subst v t -> a -> a
