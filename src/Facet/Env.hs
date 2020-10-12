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
import           Facet.Core.Value
import           Facet.Name
import           Facet.Syntax
import           Prelude hiding (lookup)

newtype Env m = Env { getEnv :: Map.Map DName (MName ::: Value m Level) }
  deriving (Monoid, Semigroup)

fromList :: [(DName, MName ::: Value m Level)] -> Env m
fromList = coerce (Map.fromList @DName @(MName ::: Value _ Level))

lookup :: DName -> Env m -> Maybe (MName ::: Value m Level)
lookup = coerce (Map.lookup @DName @(MName ::: Value _ Level))

insert :: QName ::: Value m Level -> Env m -> Env m
insert (m :.: d ::: _T) = Env . Map.insert d (m ::: _T) . getEnv
