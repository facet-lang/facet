module Facet.Surface.Type.Class
( Type(..)
) where

import Facet.Name
import Facet.Surface.Type.Expr (Interface, Kind, Mul)

-- FIXME: interface for annotating types/terms
class Type r where
  var :: QName -> r
  string :: r
  -- FIXME: how do we annotate the kind?
  forAll :: Name -> Kind -> (r -> r) -> r
  arrow :: Maybe Name -> Maybe Mul -> r -> r -> r
  -- FIXME: how do we annotate the interface?
  comp :: [Interface r] -> r -> r
  tapp :: r -> r -> r
