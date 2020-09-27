{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
module Facet.Core
( Type(..)
, Expr(..)
, Interpret(..)
) where

import Control.Applicative (liftA2)

class Type ty where
  _Type :: ty
  _Unit :: ty

  -- | Universal quantification.
  (>=>) :: ty -> (ty -> ty) -> ty
  infixr 1 >=>
  (-->) :: ty -> ty -> ty
  infixr 2 -->

  (.$) :: ty -> ty -> ty
  infixl 9 .$
  (.*) :: ty -> ty -> ty
  infixl 7 .*
  -- FIXME: tupling/unit should take a list of types

instance Type ty => Type (a -> ty) where
  _Type = pure _Type
  _Unit = pure _Unit

  t >=> b = \ a -> t a >=> \ x -> b (pure x) a
  (-->) = liftA2 (-->)

  (.$) = liftA2 (.$)
  (.*) = liftA2 (.*)


class Expr expr where
  lam0 :: (expr a -> expr b) -> expr (a -> b)
  ($$) :: expr (a -> b) -> expr a -> expr b
  infixl 9 $$


class Interpret f where
  interpret :: Type ty => f ty -> ty
