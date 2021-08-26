{-# LANGUAGE FunctionalDependencies #-}
module Facet.Surface.Type.Class
( Kind(..)
, Type(..)
, Interface(..)
) where

import Facet.Name
import Facet.Snoc
import Facet.Surface.Type.Expr (Mul)

class Kind f r | r -> f where
  ktype :: r
  kinterface :: r
  karrow :: Maybe Name -> f r -> f r -> r

class Type f r | r -> f where
  var :: QName -> r
  string :: r
  forAll :: Name -> f r -> (f r -> f r) -> r
  arrow :: Maybe Name -> Maybe Mul -> f r -> f r -> r
  comp :: [f r] -> f r -> r
  tapp :: f r -> f r -> r

class Interface f r | r -> f where
  interface :: QName -> Snoc (f r) -> r
