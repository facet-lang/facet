{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Type
( Type(..)
, Interpret(..)
, Equal(..)
, Unify(..)
) where

import qualified Facet.Core as C

data Type a
  = Var a
  | Type
  | Unit
  | Type a :* Type a
  | Type a :$ Type a
  | Type a :-> Type a
  | ForAll (Type a) (Type a -> Type a)

infixl 7 :*
infixr 0 :->
infixl 9 :$

instance C.Type (Type a) where
  _Type = Type
  _Unit = Unit
  (.*) = (:*)
  (-->) = (:->)
  (>=>) = ForAll
  (.$) = (:$)

class Interpret f where
  interpret :: C.Type ty => f ty -> ty

instance Interpret Type where
  interpret = \case
    Var v -> v
    Type -> C._Type
    Unit -> C._Unit
    f :$ a -> interpret f C..$ interpret a
    l :* r -> interpret l C..* interpret r
    a :-> b -> interpret a C.--> interpret b
    ForAll t b -> interpret t C.>=> interpret . b . Var


newtype Equal ty = Equal { runEqual :: Type ty -> Bool }

newtype Unify ty = Unify { runUnify :: Type ty -> ty }


data ForAll ty = ForAll' ty (ty -> ty)

instance Interpret ForAll where
  interpret (ForAll' t b) = t C.>=> b

data Match f a
  = N a
  | Y (f a)

instance Interpret f => Interpret (Match f) where
  interpret = \case
    N t -> t
    Y f -> interpret f

fromMatch :: (C.Type ty, Interpret f) => Match f ty -> ty
fromMatch = \case
  N t -> t
  Y f -> interpret f

instance C.Type ty => C.Type (Match ForAll ty) where
  _Type = N C._Type
  _Unit = N C._Unit
  l .* r = N (fromMatch l C..* fromMatch r)
  f .$ a = N (fromMatch f C..$ fromMatch a)
  a --> b = N (fromMatch a C.--> fromMatch b)
  t >=> b = Y (ForAll' (fromMatch t) (fromMatch . b . N))
