module Facet.Surface.Expr
( Expr(..)
) where

import           Facet.Name
import qualified Facet.Surface as S

data Expr
  = Global S.EName
  | Bound Name
  | Lam Name Expr
  | Expr :$ Expr
  | Unit
  | Expr :* Expr

infixl 9 :$
infixl 7 :*

instance S.Expr Expr where
  global = Global
  bound = Bound
  lam = Lam
  ($$) = (:$)
  unit = Unit
  (**) = (:*)
