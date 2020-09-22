module Facet.Elab
( Elab(..)
) where

import qualified Data.Map as Map
import qualified Facet.Syntax.Untyped as U
import           Facet.Type

type Env = Map.Map U.Name Type

newtype Elab = Elab { runElab :: Env -> Type -> Maybe Type }

instance U.Global Elab where
  global n = Elab $ \ env ty -> Map.lookup n env >>= unify ty


-- FIXME: handle foralls
unify :: Type -> Type -> Maybe Type
unify t1 t2 = case (t1, t2) of
  (Type,      Type)      -> Just Type
  (a1 :-> b1, a2 :-> b2) -> (:->) <$> unify a1 a2 <*> unify b1 b2
  _                      -> Nothing
