module Facet.Elab
( elab
, check
, synth
, Elab(..)
) where

import           Control.Monad ((<=<))
import qualified Data.Map as Map
import qualified Facet.Syntax.Untyped as U
import           Facet.Type

type Env = Map.Map U.Name Type
type Result = Maybe Type

elab :: Maybe Type -> Elab -> Env -> Result
elab = flip runElab

check :: Type -> Elab -> Env -> Result
check = elab . Just

synth :: Type -> Elab -> Env -> Result
synth = elab . Just

newtype Elab = Elab { runElab :: Maybe Type -> Env -> Result }

instance U.Global Elab where
  global n = Elab $ \ ty -> maybe pure unify ty <=< Map.lookup n


-- FIXME: handle foralls
unify :: Type -> Type -> Maybe Type
unify t1 t2 = case (t1, t2) of
  (Type,      Type)      -> Just Type
  (a1 :-> b1, a2 :-> b2) -> (:->) <$> unify a1 a2 <*> unify b1 b2
  _                      -> Nothing
