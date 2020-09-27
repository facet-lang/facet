{-# LANGUAGE RankNTypes #-}
module Facet.Core.Lifted
( -- * Types
  C.Type
, _Type
, _Unit
, (>=>)
, (.$)
, (-->)
, (.*)
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
, weaken
) where

import           Control.Applicative (liftA2)
import qualified Facet.Core as C
import           Facet.Env

-- Types

_Type :: (C.Type ty, Applicative env) => env ty
_Type = pure C._Type

_Unit :: (C.Type ty, Applicative env) => env ty
_Unit = pure C._Unit


(>=>)
  :: (C.Type ty, Applicative m, Permutable env)
  => m (env ty)
  -> (forall env' . Permutable env' => Extends env env' -> env' ty -> m (env' ty))
  -> m (env ty)
t >=> b = liftA2 (C.>=>) <$> t <*> liftBinder b

infixr 1 >=>

(.$) :: (C.Type ty, Applicative env) => env ty -> env ty -> env ty
(.$) = liftA2 (C..$)

infixl 9 .$


(-->) :: (C.Type ty, Applicative env) => env ty -> env ty -> env ty
(-->) = liftA2 (C.-->)

infixr 2 -->

(.*) :: (C.Type ty, Applicative env) => env ty -> env ty -> env ty
(.*) = liftA2 (C..*)

infixl 7 .*


-- Expressions

lam0
  :: (Applicative m, Permutable env, C.Expr expr)
  => (forall env' . Permutable env' => Extends env env' -> env' expr -> m (env' expr))
  -> m (env expr)
lam0 f = fmap C.lam0 <$> liftBinder f
