{-# LANGUAGE GADTs #-}
module Facet.Expr
( Expr(..)
) where

class Expr repr where
  lam :: (repr a -> repr b) -> repr (a -> b)
  ($$) :: repr (a -> b) -> repr a -> repr b
  infixl 9 $$
