{-# LANGUAGE FunctionalDependencies #-}
module Facet.Type
( Type(..)
, TypeSig(..)
) where

class Type ty where
  (-->) :: ty -> ty

class TypeSig ty sig | sig -> ty where
  (>->) :: ty -> (ty -> sig) -> sig
