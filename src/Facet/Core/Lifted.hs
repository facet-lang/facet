{-# LANGUAGE RankNTypes #-}
module Facet.Core.Lifted
( C.Type
, _Type
, _Unit
, (.*)
, (.$)
, (-->)
, (>=>)
, C.Expr(($$))
, lam0
) where

import           Control.Applicative (liftA2)
import qualified Facet.Core as C
import           Facet.Functor.C

_Type :: (Applicative m, C.Type ty) => m ty
_Type = pure C._Type

_Unit :: (Applicative m, C.Type ty) => m ty
_Unit = pure C._Unit

(.*) :: (Applicative m, C.Type ty) => m ty -> m ty -> m ty
(.*) = liftA2 (C..*)

(.$) :: (Applicative m, C.Type ty) => m ty -> m ty -> m ty
(.$) = liftA2 (C..$)

(-->) :: (Applicative m, C.Type ty) => m ty -> m ty -> m ty
(-->) = liftA2 (C.-->)

-- | Universal quantification.
(>=>)
  :: (Applicative m, Permutable env, C.Type ty)
  => m (env ty)
  -> (forall env' . Extends env env' => env' ty -> m (env' ty))
  -> m (env ty)
t >=> b = liftA2 (C.>=>) <$> t <*> (getC <$> b (C (pure id)))

infixr 1 >=>

lam0
  :: (Applicative m, Permutable env, C.Expr expr)
  => (forall env' . Extends env env' => env' expr -> m (env' expr))
  -> m (env expr)
lam0 f = fmap C.lam0 . getC <$> f (C (pure id))
