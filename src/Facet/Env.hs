module Facet.Env
( Env(..)
) where

import qualified Data.Map as Map
import qualified Data.Text as T
import           Facet.Type

newtype Env = Env { getEnv :: Map.Map T.Text Type }
