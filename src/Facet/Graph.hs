module Facet.Graph
( Graph(..)
) where

import qualified Data.Map as Map
import           Facet.Core
import           Facet.Name

newtype Graph = Graph { getGraph :: Map.Map MName Module }
