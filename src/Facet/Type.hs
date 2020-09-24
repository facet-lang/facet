{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Type
( Type(..)
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

instance C.Interpret Type where
  interpret = \case
    Var v -> v
    Type -> C._Type
    Unit -> C._Unit
    f :$ a -> C.interpret f C..$ C.interpret a
    l :* r -> C.interpret l C..* C.interpret r
    a :-> b -> C.interpret a C.--> C.interpret b
    ForAll t b -> C.interpret t C.>=> C.interpret . b . Var


newtype Equal ty = Equal { runEqual :: Type ty -> Bool }

newtype Unify ty = Unify { runUnify :: Type ty -> ty }


data ForAll ty = ForAll' ty (ty -> ty)

instance C.Interpret ForAll where
  interpret (ForAll' t b) = t C.>=> b

instance C.Type ty => C.Type (C.Match ForAll ty) where
  _Type = C.N C._Type
  _Unit = C.N C._Unit
  l .* r = C.N (C.interpret l C..* C.interpret r)
  f .$ a = C.N (C.interpret f C..$ C.interpret a)
  a --> b = C.N (C.interpret a C.--> C.interpret b)
  t >=> b = C.Y (ForAll' (C.interpret t) (C.interpret . b . C.N))
