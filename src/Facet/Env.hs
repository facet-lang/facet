{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Env
( Env(..)
, fromList
, lookup
) where

import           Data.Coerce
import qualified Data.Map as Map
import           Facet.Core.Type
import           Facet.Name
import           Facet.Syntax
import           Prelude hiding (lookup)

newtype Env = Env { getEnv :: Map.Map DName (MName ::: Type) }
  deriving (Monoid, Semigroup)

fromList :: [(DName, MName ::: Type)] -> Env
fromList = coerce (Map.fromList @DName @(MName ::: Type))

lookup :: DName -> Env -> Maybe (MName ::: Type)
lookup = coerce (Map.lookup @DName @(MName ::: Type))
