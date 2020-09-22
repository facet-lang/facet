module Facet.Elab
( Elab(..)
) where

import           Control.Monad (guard)
import qualified Data.Map as Map
import qualified Facet.Syntax.Untyped as U
import           Facet.Type

type Env = Map.Map U.Name Type

newtype Elab = Elab { runElab :: Env -> Type -> Maybe () }

instance U.Global Elab where
  global n = Elab $ \ env ty -> Map.lookup n env >>= unify ty


unify :: Type -> Type -> Maybe ()
unify t1 t2 = guard $ aeq t1 t2

-- FIXME: handle foralls
aeq :: Type -> Type -> Bool
aeq Type        Type        = True
aeq (a1 :-> b1) (a2 :-> b2) = aeq a1 a2 && aeq b1 b2
aeq _           _           = False
