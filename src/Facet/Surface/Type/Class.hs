module Facet.Surface.Type.Class
( Type(..)
, Interface(..)
) where

import Facet.Kind
import Facet.Name
import Facet.Snoc
import Facet.Surface.Type.Expr (Mul)

-- FIXME: interface for annotating types/terms
class Type r where
  var :: QName -> r
  string :: r
  forAll :: Name -> Kind -> (r -> r) -> r
  arrow :: Maybe Name -> Maybe Mul -> r -> r -> r
  comp :: [r] -> r -> r
  tapp :: r -> r -> r

class Interface r where
  interface :: QName -> Snoc r -> r
