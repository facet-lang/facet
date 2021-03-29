module Facet.Subst
( -- * Substitution
  Subst(..)
, insert
, lookupMeta
, solveMeta
, declareMeta
, metas
) where

import           Control.Monad (join)
import qualified Data.IntMap as IntMap
import           Facet.Name
import           Facet.Syntax

-- Substitution

newtype Subst t = Subst (IntMap.IntMap (Maybe t))
  deriving (Monoid, Semigroup)

insert :: Meta -> Maybe t -> Subst t -> Subst t
insert (Meta i) t (Subst metas) = Subst (IntMap.insert i t metas)

lookupMeta :: Meta -> Subst t -> Maybe t
lookupMeta (Meta i) (Subst metas) = join (IntMap.lookup i metas)

solveMeta :: Meta -> t -> Subst t -> Subst t
solveMeta (Meta i) t (Subst metas) = Subst (IntMap.update (const (Just (Just t))) i metas)

declareMeta :: Subst t -> (Subst t, Meta)
declareMeta (Subst metas) = (Subst (IntMap.insert v Nothing metas), Meta v) where
  v = maybe 0 (succ . fst . fst) (IntMap.maxViewWithKey metas)

metas :: Subst t -> [Meta :=: Maybe t]
metas (Subst metas) = map (\ (k, v) -> Meta k :=: v) (IntMap.toList metas)
