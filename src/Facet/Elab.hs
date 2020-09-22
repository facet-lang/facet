module Facet.Elab
( elab
, check
, synth
, Elab(..)
) where

import           Control.Carrier.Reader
import           Control.Effect.Empty
import qualified Data.Map as Map
import qualified Facet.Syntax.Untyped as U
import           Facet.Type

type Env = Map.Map U.Name Type

elab :: Maybe Type -> Elab -> ReaderC Env Maybe Type
elab = flip runElab

check :: Type -> Elab -> ReaderC Env Maybe Type
check = elab . Just

synth :: Elab -> ReaderC Env Maybe Type
synth = elab Nothing

newtype Elab = Elab { runElab :: Maybe Type -> ReaderC Env Maybe Type }

instance U.Global Elab where
  global n = Elab $ \ ty -> maybe pure unify ty =<< ReaderC (Map.lookup n)


-- FIXME: handle foralls
unify :: Type -> Type -> ReaderC Env Maybe Type
unify t1 t2 = case (t1, t2) of
  (Type,      Type)      -> pure Type
  (a1 :-> b1, a2 :-> b2) -> (:->) <$> unify a1 a2 <*> unify b1 b2
  _                      -> empty
