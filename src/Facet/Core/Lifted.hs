{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core.Lifted
( C.Type(_Type, _Unit, (.$), (.*), (-->))
, (>=>)
, C.Expr(($$))
, lam0
) where

import qualified Facet.Core as C
import           Facet.Functor.C

-- | Universal quantification.
(>=>)
  :: (Applicative m, Permutable env, C.Type ty)
  => (m :.: env) ty
  -> (forall env' . Permutable env' => (env :.: env') ty -> (m :.: env :.: env') ty)
  -> (m :.: env) ty
t >=> b = (C.>=>) <$> t <*> C (getC <$> getC (b (C (pure id))))

infixr 1 >=>

lam0
  :: (Applicative m, Permutable env, C.Expr expr)
  => (forall env' . Permutable env' => (env :.: env') expr -> (m :.: env :.: env') expr)
  -> (m :.: env) expr
lam0 f = C.lam0 <$> C (getC <$> getC (f (C (pure id))))
