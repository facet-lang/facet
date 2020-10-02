{-# LANGUAGE TypeApplications #-}
module Facet.Env
( Env(..)
, fromList
, lookup
) where

import           Data.Coerce
import qualified Data.Map as Map
import qualified Data.Text as T
import           Facet.Type
import Prelude hiding (lookup)

newtype Env = Env { getEnv :: Map.Map T.Text Type }

fromList :: [(T.Text, Type)] -> Env
fromList = coerce (Map.fromList @T.Text @Type)

lookup :: T.Text -> Env -> Maybe Type
lookup = coerce (Map.lookup @T.Text @Type)
