module Facet.Elab
( Elab(..)
) where

import qualified Data.Map as Map
import qualified Facet.Syntax.Untyped as U
import           Facet.Type

type Env = Map.Map U.Name ()

newtype Elab = Elab { runElab :: Env -> Type -> Maybe () }
