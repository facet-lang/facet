{-# LANGUAGE GADTs #-}
module Facet.Expr
( Expr(..)
  -- * Examples
, id'
) where

class Expr repr where
  lam :: [repr a -> repr b] -> repr (a -> b)
  ($$) :: repr (a -> b) -> repr a -> repr b
  infixl 9 $$


-- Examples

id' :: Expr repr => repr (a -> a)
id' = lam [id]
