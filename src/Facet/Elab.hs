module Facet.Elab
( check
, synth
, Elab(..)
) where

import           Control.Carrier.Reader
import           Control.Effect.Empty
import qualified Data.Map as Map
import qualified Facet.Syntax.Untyped as U
import           Facet.Type

type Env = Map.Map U.Name Type

check :: Elab -> Type -> ReaderC Env Maybe Type
check m = elab m . Just

synth :: Elab -> ReaderC Env Maybe Type
synth m = elab m Nothing

newtype Elab = Elab { elab :: Maybe Type -> ReaderC Env Maybe Type }

instance U.Global Elab where
  global n = Elab $ \ ty -> maybe pure unify ty =<< ReaderC (Map.lookup n)

instance U.App Elab where
  f $$ a = Elab $ \ _T -> do
    _F <- synth f
    case _F of
      _A :-> _T' -> do
        _ <- check a _A
        maybe pure unify _T _T'
      _ -> empty


-- FIXME: handle foralls
unify :: Type -> Type -> ReaderC Env Maybe Type
unify t1 t2 = case (t1, t2) of
  (Type,      Type)      -> pure Type
  (a1 :-> b1, a2 :-> b2) -> (:->) <$> unify a1 a2 <*> unify b1 b2
  _                      -> empty
