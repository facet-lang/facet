module Facet.Env
( Env(..)
, lookup
) where

import qualified Data.Map as Map
import qualified Data.Text as T
import           Facet.Type
import Prelude hiding (lookup)

newtype Env = Env { getEnv :: Map.Map T.Text Type }

lookup :: T.Text -> Env -> Maybe Type
lookup k = Map.lookup k . getEnv
