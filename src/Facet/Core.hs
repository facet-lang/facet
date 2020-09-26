{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
module Facet.Core
( Type(..)
, Expr(..)
, Interpret(..)
, Match(..)
, IsType(..)
, IsUnit(..)
, IsProd(..)
, IsApp(..)
, IsFunction(..)
, IsForAll(..)
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

data Match f a
  = N a
  | Y (f a)

instance Interpret f => Interpret (Match f) where
  interpret = \case
    N t -> t
    Y f -> interpret f


data IsType ty = IsType

instance Interpret IsType where
  interpret IsType = _Type

instance Type ty => Type (Match IsType ty) where
  _Type = Y IsType
  _Unit = N _Unit
  l .* r = N (interpret l .* interpret r)
  f .$ a = N (interpret f .$ interpret a)
  a --> b = N (interpret a --> interpret b)
  t >=> b = N (interpret t >=> interpret . b . N)


data IsUnit ty = IsUnit

instance Interpret IsUnit where
  interpret IsUnit = _Unit

instance Type ty => Type (Match IsUnit ty) where
  _Type = N _Type
  _Unit = Y IsUnit
  l .* r = N (interpret l .* interpret r)
  f .$ a = N (interpret f .$ interpret a)
  a --> b = N (interpret a --> interpret b)
  t >=> b = N (interpret t >=> interpret . b . N)


data IsProd ty = IsProd ty ty

instance Interpret IsProd where
  interpret (IsProd a b) = a --> b

instance Type ty => Type (Match IsProd ty) where
  _Type = N _Type
  _Unit = N _Unit
  l .* r = Y (IsProd (interpret l) (interpret r))
  f .$ a = N (interpret f .$ interpret a)
  a --> b = N (interpret a --> interpret b)
  t >=> b = N (interpret t >=> interpret . b . N)


data IsApp ty = IsApp ty ty

instance Interpret IsApp where
  interpret (IsApp a b) = a --> b

instance Type ty => Type (Match IsApp ty) where
  _Type = N _Type
  _Unit = N _Unit
  l .* r = N (interpret l .* interpret r)
  f .$ a = Y (IsApp (interpret f) (interpret a))
  a --> b = N (interpret a --> interpret b)
  t >=> b = N (interpret t >=> interpret . b . N)


data IsFunction ty = IsFunction ty ty

instance Interpret IsFunction where
  interpret (IsFunction a b) = a --> b

instance Type ty => Type (Match IsFunction ty) where
  _Type = N _Type
  _Unit = N _Unit
  l .* r = N (interpret l .* interpret r)
  f .$ a = N (interpret f .$ interpret a)
  a --> b = Y (IsFunction (interpret a) (interpret b))
  t >=> b = N (interpret t >=> interpret . b . N)


data IsForAll ty = IsForAll ty (ty -> ty)

instance Interpret IsForAll where
  interpret (IsForAll t b) = t >=> b

instance Type ty => Type (Match IsForAll ty) where
  _Type = N _Type
  _Unit = N _Unit
  l .* r = N (interpret l .* interpret r)
  f .$ a = N (interpret f .$ interpret a)
  a --> b = N (interpret a --> interpret b)
  t >=> b = Y (IsForAll (interpret t) (interpret . b . N))
