{-# LANGUAGE FunctionalDependencies #-}
module Facet.Module
( DefName
, Module(..)
) where

type DefName = String

class Module def mod | mod -> def where
  (.=) :: DefName -> (def a -> def a) -> mod (def a)
