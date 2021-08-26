module Facet.Surface.Type.Class
( Kind(..)
, Type(..)
, Interface(..)
) where

import Facet.Name
import Facet.Snoc
import Facet.Surface.Type.Expr (Mul)

class Kind r where
  ktype :: r
  kinterface :: r
  karrow :: Maybe Name -> r -> r -> r

-- FIXME: interface for annotating types/terms
class Type r where
  var :: QName -> r
  string :: r
  forAll :: Name -> r -> (r -> r) -> r
  arrow :: Maybe Name -> Maybe Mul -> r -> r -> r
  comp :: [r] -> r -> r
  tapp :: r -> r -> r

class Interface r where
  interface :: QName -> Snoc r -> r
