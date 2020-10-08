module Facet.Substitution
( Substitution(..)
, insert
) where

import qualified Data.IntMap as IntMap
import           Facet.Name

newtype Substitution a = Substitution { getSubstitution :: IntMap.IntMap a }

insert :: Name a -> t -> Substitution t -> Substitution t
insert n t = Substitution . IntMap.insert (id' n) t . getSubstitution
