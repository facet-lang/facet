module Facet.Substitution
( Substitution(..)
, instantiate
) where

import qualified Data.IntMap as IntMap
import           Facet.Name

newtype Substitution a = Substitution { getSubstitution :: IntMap.IntMap a }

instantiate :: Name a -> t -> Substitution t -> Substitution t
instantiate n t = Substitution . IntMap.insert (id' n) t . getSubstitution
