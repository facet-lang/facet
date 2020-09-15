{-# LANGUAGE FunctionalDependencies #-}
module Facet.Module
( DeclName
, Module(..)
, Decl(..)
) where

type DeclName = String

class Decl expr ty decl => Module expr ty decl mod | mod -> decl ty expr where
  (.:) :: DeclName -> (decl a -> decl a) -> mod (decl a)
  infix 0 .:

class Decl expr ty decl | decl -> ty expr where
  forAll :: (ty -> decl a) -> decl a
  (>->) :: ty -> (expr a -> decl a) -> decl a
