{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Facet.Substitution
( Substitution(..)
, singleton
, insert
, member
, lookup
) where

import           Data.Coerce
import qualified Data.IntMap as IntMap
import           Facet.Name
import           Prelude hiding (lookup)

newtype Substitution a = Substitution { getSubstitution :: IntMap.IntMap a }
  deriving (Foldable, Functor)

singleton :: Name a -> t -> Substitution t
singleton n = coerce . IntMap.singleton (id' n)

insert :: Name a -> t -> Substitution t -> Substitution t
insert n = coerce . IntMap.insert (id' n)

member :: Name a -> Substitution t -> Bool
member n = IntMap.member (id' n) . getSubstitution

lookup :: Name a -> Substitution t -> Maybe t
lookup n = IntMap.lookup (id' n) . getSubstitution
