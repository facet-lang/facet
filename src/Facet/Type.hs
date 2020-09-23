{-# LANGUAGE LambdaCase #-}
module Facet.Type
( Type(..)
, interpret
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

interpret :: C.Type ty => Type ty -> ty
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
