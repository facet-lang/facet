module Facet.Elab
( elab
, Elab(..)
) where

import           Control.Monad ((<=<))
import qualified Data.Map as Map
import qualified Facet.Syntax.Untyped as U
import           Facet.Type

type Env = Map.Map U.Name Type
type Result = Maybe Type

elab :: Maybe Type -> Env -> Elab -> Result
elab g e m = runElab m g e

newtype Elab = Elab { runElab :: Maybe Type -> Env -> Result }

instance U.Global Elab where
  global n = Elab $ \ ty -> maybe pure unify ty <=< Map.lookup n


-- FIXME: handle foralls
unify :: Type -> Type -> Maybe Type
unify t1 t2 = case (t1, t2) of
  (Type,      Type)      -> Just Type
  (a1 :-> b1, a2 :-> b2) -> (:->) <$> unify a1 a2 <*> unify b1 b2
  _                      -> Nothing
