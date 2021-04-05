module Facet.Core.Interface
( Interface(..)
, Signature(..)
, fromInterfaces
, singleton
, interfaces
, mapSignature
) where

import qualified Data.Set as Set
import           Facet.Name
import           Facet.Snoc

data Interface a = Interface RName (Snoc a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

newtype Signature a = Signature { getSignature :: Set.Set (Interface a) }
  deriving (Eq, Foldable, Monoid, Ord, Semigroup, Show)

fromInterfaces :: Ord a => [Interface a] -> Signature a
fromInterfaces = Signature . Set.fromList

singleton :: Interface a -> Signature a
singleton = Signature . Set.singleton

interfaces :: Signature a -> [Interface a]
interfaces = Set.toList . getSignature

mapSignature :: Ord b => (a -> b) -> Signature a -> Signature b
mapSignature f = Signature . Set.map (fmap f) . getSignature
