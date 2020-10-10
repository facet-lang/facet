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

newtype Env m = Env { getEnv :: Map.Map DName (MName ::: Type m Level) }
  deriving (Monoid, Semigroup)

fromList :: [(DName, MName ::: Type m Level)] -> Env m
fromList = coerce (Map.fromList @DName @(MName ::: Type _ Level))

lookup :: DName -> Env m -> Maybe (MName ::: Type m Level)
lookup = coerce (Map.lookup @DName @(MName ::: Type _ Level))

insert :: QName ::: Type m Level -> Env m -> Env m
insert (m :.: d ::: _T) = Env . Map.insert d (m ::: _T) . getEnv
