module Facet.Surface.Type.Class
( Kind(..)
, Type(..)
) where

import Facet.Name
import Facet.Surface.Type.Expr (Interface, Mul)

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
  -- FIXME: how do we annotate the interface?
  comp :: [Interface r] -> r -> r
  tapp :: r -> r -> r
