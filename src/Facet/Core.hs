{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Core
( Type(..)
, Expr(..)
, Interpret(..)
, Match(..)
, ForAll(..)
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
  lam0 :: (expr -> expr) -> expr
  ($$) :: expr -> expr -> expr
  infixl 9 $$


class Interpret f where
  interpret :: Type ty => f ty -> ty

data Match f a
  = N a
  | Y (f a)

instance Interpret f => Interpret (Match f) where
  interpret = \case
    N t -> t
    Y f -> interpret f


data ForAll ty = ForAll ty (ty -> ty)

instance Interpret ForAll where
  interpret (ForAll t b) = t >=> b

instance Type ty => Type (Match ForAll ty) where
  _Type = N _Type
  _Unit = N _Unit
  l .* r = N (interpret l .* interpret r)
  f .$ a = N (interpret f .$ interpret a)
  a --> b = N (interpret a --> interpret b)
  t >=> b = Y (ForAll (interpret t) (interpret . b . N))
