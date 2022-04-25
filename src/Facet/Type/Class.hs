module Facet.Type.Class
( -- * Types
  Type(..)
, forAllA
) where

import Data.Foldable (foldl')
import Facet.Functor.Compose
import Facet.Interface (Signature)
import Facet.Kind (Kind)
import Facet.Name (Level, Meta, Name)
import Facet.Syntax (Var, type (~>))

-- Types

class Type r where
  string :: r
  forAll :: Name -> Kind -> (r -> r) -> r
  arrow :: Maybe Name -> r -> r -> r
  var :: Var (Either Meta Level) -> r
  ($$) :: r -> r -> r
  infixl 9 $$
  ($$$) :: Foldable t => Var (Either Meta Level) -> t r -> r
  h $$$ sp = foldl' ($$) (var h) sp
  infixl 9 $$$
  (|-) :: Signature r -> r -> r
  infixr 9 |-

forAllA :: (Applicative m, Applicative i, Type r) => Name -> Kind -> (forall j . Applicative j => (i ~> j) -> j r -> m (j r)) -> m (i r)
forAllA n k = binder (forAll n k)
