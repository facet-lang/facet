module Facet.Env
( Env
) where

import qualified Data.Map as Map
import qualified Data.Text as T
import           Facet.Type

type Env = Map.Map T.Text Type
