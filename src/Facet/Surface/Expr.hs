{-# LANGUAGE DeriveTraversable #-}
module Facet.Surface.Expr
( Expr(..)
) where

import           Facet.Name
import qualified Facet.Surface as S

newtype Expr = In { out :: ExprF Expr }

data ExprF e
  = Global S.EName
  | Bound Name
  | Lam Name e
  | e :$ e
  | Unit
  | e :* e
  deriving (Foldable, Functor, Traversable)

infixl 9 :$
infixl 7 :*

instance S.Expr Expr where
  global = In . Global
  bound = In . Bound
  lam = fmap In . Lam
  ($$) = fmap In . (:$)
  unit = In Unit
  (**) = fmap In . (:*)
