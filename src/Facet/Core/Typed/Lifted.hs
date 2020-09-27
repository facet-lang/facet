{-# LANGUAGE RankNTypes #-}
module Facet.Core.Typed.Lifted
( C.Type(_Type, _Unit, (.$), (.*), (-->))
, (>=>)
) where

import           Control.Applicative (liftA2)
import qualified Data.Kind as K
import qualified Facet.Core.Typed as C
import           Facet.Env

(>=>)
  :: (C.Type ty, Applicative m, Permutable env)
  => m (env (ty K.Type))
  -> (forall env' . Permutable env' => Extends env env' -> env' (ty k1) -> m (env' (ty k2)))
  -> m (env (ty (k1 -> k2)))
t >=> b = liftA2 (C.>=>) <$> t <*> liftBinder b

infixr 1 >=>
