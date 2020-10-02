{-# LANGUAGE DeriveTraversable #-}
module Facet.Surface.Expr
( Expr(..)
, ExprF(..)
, fold
) where

import           Control.Effect.Parser.Span (Span)
import           Facet.Name
import qualified Facet.Surface as S

newtype Expr = In { out :: ExprF Expr }

data ExprF e
  = Free S.EName
  | Bound Name
  | Lam Name e
  | e :$ e
  | Unit
  | e :* e
  | Ann Span e
  deriving (Foldable, Functor, Traversable)

infixl 9 :$
infixl 7 :*

instance S.Expr Expr where
  global = In . Free
  bound = In . Bound
  lam = fmap In . Lam
  ($$) = fmap In . (:$)
  unit = In Unit
  (**) = fmap In . (:*)


fold :: (ExprF a -> a) -> Expr -> a
fold alg = go
  where
  go = alg . fmap go . out
