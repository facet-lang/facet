module Facet.Syntax.Untyped
( Expr(..)
, Err(..)
) where

class Expr repr where
  lam0 :: (repr -> repr) -> repr
  lam :: (Either repr (repr, repr -> repr) -> repr) -> repr
  ($$) :: repr -> repr -> repr
  infixl 9 $$

class Err expr where
  err :: expr
