{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Env
( Env(..)
, fromList
, lookup
, insert
) where

import           Data.Coerce
import qualified Data.Map as Map
import           Facet.Core.Type
import           Facet.Name
import           Facet.Syntax
import           Prelude hiding (lookup)

newtype Env m = Env { getEnv :: Map.Map DName (MName ::: Type m) }
  deriving (Monoid, Semigroup)

fromList :: [(DName, MName ::: Type m)] -> Env m
fromList = coerce (Map.fromList @DName @(MName ::: Type _))

lookup :: DName -> Env m -> Maybe (MName ::: Type m)
lookup = coerce (Map.lookup @DName @(MName ::: Type _))

insert :: QName ::: Type m -> Env m -> Env m
insert (m :.: d ::: _T) = Env . Map.insert d (m ::: _T) . getEnv
