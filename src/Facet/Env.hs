{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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

newtype Env a = Env { getEnv :: Map.Map DName (MName :=: (Maybe a ::: a)) }
  deriving (Monoid, Semigroup)

fromList :: [(DName, MName :=: Maybe a ::: a)] -> Env a
fromList = Env . Map.fromList

lookup :: DName -> Env a -> Maybe (MName :=: Maybe a ::: a)
lookup k = Map.lookup k . getEnv

insert :: QName :=: Maybe a ::: a -> Env a -> Env a
insert (m :.: d :=: v ::: _T) = Env . Map.insert d (m :=: v ::: _T) . getEnv
