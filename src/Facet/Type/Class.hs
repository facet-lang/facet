module Facet.Type.Class
( -- * Types
  Type(..)
, forAllA
) where

import Facet.Functor.Compose
import Facet.Interface (Signature)
import Facet.Kind (Kind)
import Facet.Name (LName, Level, Meta, Name)
import Facet.Syntax (Var, type (~>))
import Facet.Usage (Quantity)

-- Types

class Type r where
  string :: r
  forAll :: Name -> Kind -> (r -> r) -> r
  arrow :: Maybe Name -> Quantity -> r -> r -> r
  var :: Var (Either Meta (LName Level)) -> r
  ($$) :: r -> r -> r
  infixl 9 $$
  (|-) :: Signature r -> r -> r
  infixr 9 |-

forAllA :: (Applicative m, Applicative i, Type r) => Name -> Kind -> (forall j . Applicative j => (i ~> j) -> j r -> m (j r)) -> m (i r)
forAllA n k b = fmap (forAll n k) . runC <$> b liftCOuter (liftCInner id)