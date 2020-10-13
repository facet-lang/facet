{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Env
( Env(..)
, fromList
, lookup
, insert
) where

import qualified Data.Map as Map
import           Facet.Name
import           Facet.Syntax
import           Prelude hiding (lookup)

newtype Env a = Env { getEnv :: Map.Map DName (MName ::: a) }
  deriving (Monoid, Semigroup)

fromList :: [(DName, MName ::: a)] -> Env a
fromList = Env . Map.fromList @DName @(MName ::: _)

lookup :: DName -> Env a -> Maybe (MName ::: a)
lookup k = Map.lookup @DName @(MName ::: _) k . getEnv

insert :: QName ::: a -> Env a -> Env a
insert (m :.: d ::: _T) = Env . Map.insert d (m ::: _T) . getEnv
