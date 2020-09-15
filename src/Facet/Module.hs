{-# LANGUAGE FunctionalDependencies #-}
module Facet.Module
( DeclName
, Module(..)
, Decl(..)
) where

type DeclName = String

class Decl ty decl => Module ty decl mod | mod -> decl ty where
  (.:) :: DeclName -> (decl a -> decl a) -> mod (decl a)
  infix 0 .:

class Decl ty decl | decl -> ty where
  forAll :: (ty -> decl a) -> decl a
  (>->) :: ty -> (ty -> decl a) -> decl a
