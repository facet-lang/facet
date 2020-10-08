{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Facet.Substitution
( Substitution(..)
, empty
, singleton
, insert
, member
, lookup
, Substitutable(..)
) where

import           Data.Coerce
import qualified Data.IntMap as IntMap
import           Facet.Name
import           Prelude hiding (lookup)

newtype Substitution a = Substitution { getSubstitution :: IntMap.IntMap a }
  deriving (Foldable, Functor)

empty :: Substitution t
empty = Substitution IntMap.empty

singleton :: Name a -> t -> Substitution t
singleton n = coerce . IntMap.singleton (id' n)

insert :: Name a -> t -> Substitution t -> Substitution t
insert n = coerce . IntMap.insert (id' n)

member :: Name a -> Substitution t -> Bool
member n = IntMap.member (id' n) . getSubstitution

lookup :: Name a -> Substitution t -> Maybe t
lookup n = IntMap.lookup (id' n) . getSubstitution


class Substitutable t where
  subst :: Substitution t -> t -> t
