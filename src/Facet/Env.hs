module Facet.Env
( Env(..)
, fromList
, lookup
) where

import qualified Data.Map as Map
import qualified Data.Text as T
import           Facet.Type
import Prelude hiding (lookup)

newtype Env = Env { getEnv :: Map.Map T.Text Type }

fromList :: [(T.Text, Type)] -> Env
fromList = Env . Map.fromList

lookup :: T.Text -> Env -> Maybe Type
lookup k = Map.lookup k . getEnv
