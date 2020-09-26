{-# LANGUAGE GADTs #-}
module Facet.Type.Typed
( Type(..)
) where

data Type a where
  Type :: Type () -- FIXME: Data.Kind.Type?
  Unit :: Type ()
  (:->) :: Type a -> Type b -> Type (a -> b)
  (:$) :: Type (a -> b) -> Type a -> Type b
  (:*) :: Type a -> Type b -> Type (a, b)
  -- FIXME: how is this supposed to work?
  ForAll :: Type a -> (Type a -> Type b) -> Type b

infixl 7 :*
infixr 0 :->
infixl 9 :$
