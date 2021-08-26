module Facet.Type.Class
( -- * Types
  Type(..)
) where

import Facet.Interface (Signature)
import Facet.Kind (Kind)
import Facet.Name (LName, Level, Meta, Name)
import Facet.Syntax (Var)
import Facet.Usage (Quantity)

-- Types

class Type r where
  string :: r
  forAll :: Name -> Kind -> (r -> r) -> r
  arrow :: Maybe Name -> Quantity -> r -> r -> r
  var :: Var (Either Meta (LName Level)) -> r
  ($$) :: r -> r -> r
  infixl 9 $$
  comp :: Signature r -> r -> r
