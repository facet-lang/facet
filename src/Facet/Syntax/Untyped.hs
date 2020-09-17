module Facet.Syntax.Untyped
( Name
, Expr(..)
, Err(..)
) where

type Name = String

class Expr repr where
  lam0 :: (repr -> repr) -> repr
  lam :: (Either repr (repr, repr -> repr) -> repr) -> repr
  ($$) :: repr -> repr -> repr
  infixl 9 $$

  global :: Name -> repr

class Err expr where
  err :: expr
