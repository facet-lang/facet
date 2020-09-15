{-# LANGUAGE FunctionalDependencies #-}
module Facet.Module
( DeclName
, Module(..)
, Decl(..)
) where

import Facet.Type

type DeclName = String

class Decl expr ty decl => Module expr ty decl mod | mod -> decl ty expr where
  (.:) :: DeclName -> decl a -> mod (decl a)
  infixr 0 .:

class Type ty => Decl expr ty decl | decl -> ty expr where
  forAll :: (ty -> decl a) -> decl a
  (>->) :: ty -> (expr a -> decl (expr b)) -> decl (expr a -> expr b)
  (.=) :: ty -> expr a -> decl (expr a)
  infix 1 .=
