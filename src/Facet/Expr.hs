{-# LANGUAGE GADTs #-}
module Facet.Expr
( Expr(..)
) where

data Expr a where
  Lam :: (Expr a -> Expr b) -> Expr (a -> b)
