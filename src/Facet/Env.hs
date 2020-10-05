{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Env
( Env(..)
, fromList
, lookup
) where

import           Data.Coerce
import qualified Data.Map as Map
import qualified Data.Text as T
import           Facet.Core.Type
import           Facet.Name
import           Facet.Syntax
import           Prelude hiding (lookup)

newtype Env = Env { getEnv :: Map.Map T.Text (MName ::: Type) }

fromList :: [(T.Text, MName ::: Type)] -> Env
fromList = coerce (Map.fromList @T.Text @(MName ::: Type))

lookup :: T.Text -> Env -> Maybe (MName ::: Type)
lookup = coerce (Map.lookup @T.Text @(MName ::: Type))
