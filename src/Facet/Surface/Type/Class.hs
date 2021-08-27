module Facet.Surface.Type.Class
( Type(..)
, forAllA
, Interface(..)
) where

import Facet.Functor.Compose
import Facet.Kind
import Facet.Name
import Facet.Snoc
import Facet.Surface.Type.Expr (Mul)
import Facet.Syntax (type (~>))

-- FIXME: interface for annotating types/terms
class Type r where
  var :: QName -> r
  string :: r
  forAll :: Name -> Kind -> (r -> r) -> r
  arrow :: Maybe Name -> Maybe Mul -> r -> r -> r
  comp :: [r] -> r -> r
  tapp :: r -> r -> r

forAllA :: (Applicative m, Applicative i, Type r) => (m . i) Name -> (m . i) Kind -> (forall j . Applicative j => (i ~> j) -> j r -> (m . j) r) -> (m . i) r
forAllA n k b = forAll <$> n <*> k <*> mapCInner runC (b liftCOuter (liftCInner id))

class Interface r where
  interface :: QName -> Snoc r -> r
