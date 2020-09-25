{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
module Facet.Type
( Type(..)
) where

import qualified Facet.Core as C

data Type ty
  = Var ty
  | Type
  | Unit
  | Type ty :* Type ty
  | Type ty :$ Type ty
  | Type ty :-> Type ty
  | ForAll (Type ty) (Type ty -> Type ty)

infixl 7 :*
infixr 0 :->
infixl 9 :$

instance (Eq ty, Num ty) => Eq (Type ty) where
  (==) = go 0
    where
    go n = curry $ \case
      (Var a1, Var a2) -> a1 == a2
      (Type, Type) -> True
      (Unit, Unit) -> True
      (l1 :* r1, l2 :* r2) -> go n l1 l2 && go n r1 r2
      (f1 :$ a1, f2 :$ a2) -> go n f1 f2 && go n a1 a2
      (a1 :-> b1, a2 :-> b2) -> go n a1 a2 && go n b1 b2
      (ForAll t1 b1, ForAll t2 b2) -> go n t1 t2 && go (n + 1) (b1 (Var n)) (b2 (Var n))
      _ -> False

instance C.Type (Type ty) where
  _Type = Type
  _Unit = Unit
  (.*) = (:*)
  (.$) = (:$)
  (-->) = (:->)
  (>=>) = ForAll

instance C.Interpret Type where
  interpret = \case
    Var v -> v
    Type -> C._Type
    Unit -> C._Unit
    f :$ a -> C.interpret f C..$ C.interpret a
    l :* r -> C.interpret l C..* C.interpret r
    a :-> b -> C.interpret a C.--> C.interpret b
    ForAll t b -> C.interpret t C.>=> C.interpret . b . Var
