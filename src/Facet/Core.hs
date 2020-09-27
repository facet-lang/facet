{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
module Facet.Core
( Type(..)
, Expr(..)
, Interpret(..)
) where

import qualified Data.Kind as K
import           Facet.Syntax.Common
import           Unsafe.Coerce (unsafeCoerce)

class Type ty where
  _Type :: ty K.Type
  _Unit :: ty K.Type

  -- | Universal quantification.
  (>=>) :: ty K.Type -> (ty k1 -> ty k2) -> ty (k1 -> k2)
  infixr 1 >=>
  (.$) :: ty (k1 -> k2) -> ty k1 -> ty k2
  infixl 9 .$

  (-->) :: ty K.Type -> ty K.Type -> ty K.Type
  infixr 2 -->
  (.*) :: ty K.Type -> ty K.Type -> ty K.Type
  infixl 7 .*

  -- FIXME: tupling/unit should take a list of types

instance (forall r . Type (f r)) => Type (ForAll1 f) where
  _Type = Abstract1 _Type
  _Unit = Abstract1 _Unit

  t >=> b = Abstract1 $ instantiate1 t >=> instantiate1 . b . unsafeCoerce -- I *think* this is justified by the dual parametricity in ForAll1 and again in the quantified constraint. r cannot affect the operation of >=>, so we can safely coerce the argument to its universal quantification
  f .$  a = Abstract1 $ instantiate1 f .$  instantiate1 a

  a --> b = Abstract1 $ instantiate1 a --> instantiate1 b
  l .*  r = Abstract1 $ instantiate1 l .*  instantiate1 r


class Expr expr where
  lam0 :: (expr a -> expr b) -> expr (a -> b)
  ($$) :: expr (a -> b) -> expr a -> expr b
  infixl 9 $$


class Interpret f where
  interpret :: Type ty => f ty a -> ty a
