{-# LANGUAGE FunctionalDependencies #-}
module Facet.Module
( DeclName
, Module(..)
) where

type DeclName = String

class Module decl mod | mod -> decl where
  (.:) :: DeclName -> (decl a -> decl a) -> mod (decl a)
  infix 0 .:
