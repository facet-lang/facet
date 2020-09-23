{-# LANGUAGE RankNTypes #-}
module Facet.Core.Lifted
( C.Type(_Type, _Unit, (.$), (.*), (-->))
, (>=>)
, C.Expr(($$))
) where

import           Control.Applicative (liftA2)
import qualified Facet.Core as C
import           Facet.Functor.C

-- | Universal quantification.
(>=>)
  :: (Applicative m, Permutable env, C.Type ty)
  => m (env ty)
  -> (forall env' . Extends env env' => env' ty -> m (env' ty))
  -> m (env ty)
t >=> b = liftA2 (C.>=>) <$> t <*> (getC <$> b (C (pure id)))

infixr 1 >=>
