{-# LANGUAGE RankNTypes #-}
module Facet.Core.Typed.Lifted
( C.Type
, _Type
, _Unit
, (>=>)
, (.$)
, (-->)
, (.*)
) where

import           Control.Applicative (liftA2)
import qualified Data.Kind as K
import qualified Facet.Core.Typed as C
import           Facet.Env

_Type :: (C.Type ty, Applicative env) => env (ty K.Type)
_Type = pure C._Type

_Unit :: (C.Type ty, Applicative env) => env (ty K.Type)
_Unit = pure C._Unit


(>=>)
  :: (C.Type ty, Applicative m, Permutable env)
  => m (env (ty K.Type))
  -> (forall env' . Permutable env' => Extends env env' -> env' (ty k1) -> m (env' (ty k2)))
  -> m (env (ty (k1 -> k2)))
t >=> b = liftA2 (C.>=>) <$> t <*> liftBinder b

infixr 1 >=>


(.$) :: (C.Type ty, Applicative env) => env (ty (k1 -> k2)) -> env (ty k1) -> env (ty k2)
(.$) = liftA2 (C..$)

infixl 9 .$


(-->) :: (C.Type ty, Applicative env) => env (ty K.Type) -> env (ty K.Type) -> env (ty K.Type)
(-->) = liftA2 (C.-->)

infixr 2 -->


(.*) :: (C.Type ty, Applicative env) => env (ty K.Type) -> env (ty K.Type) -> env (ty K.Type)
(.*) = liftA2 (C..*)

infixl 7 .*
