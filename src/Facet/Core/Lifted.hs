{-# LANGUAGE RankNTypes #-}
module Facet.Core.Lifted
( -- * Types
  C.Type((.$), (.*), _Type, _Unit, (-->))
, (>=>)
, C.Interpret(..)
  -- * Expressions
, C.Expr(($$))
, lam0
  -- * Re-exports
, Extends(..)
, Permutable
, (>>>)
, castF
, refl
, strengthen
) where

import           Control.Applicative (liftA2)
import qualified Facet.Core as C
import           Facet.Env

-- Types

-- | Universal quantification.
(>=>)
  :: (Applicative m, Permutable env, C.Type ty)
  => m (env ty)
  -> (forall env' . Permutable env' => Extends env env' -> env' ty -> m (env' ty))
  -> m (env ty)
t >=> b = liftA2 (C.>=>) <$> t <*> liftBinder b

infixr 1 >=>


-- Expressions

lam0
  :: (Applicative m, Permutable env, C.Expr expr)
  => (forall env' . Permutable env' => Extends env env' -> env' expr -> m (env' expr))
  -> m (env expr)
lam0 f = fmap C.lam0 <$> liftBinder f
