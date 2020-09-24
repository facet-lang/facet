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
