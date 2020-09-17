module Facet.Expr.Untyped
( Expr(..)
) where

class Expr repr where
  lam :: (Either repr (repr, repr -> repr) -> repr) -> repr
  ($$) :: repr -> repr -> repr
  infixl 9 $$

  alg :: repr -> (repr -> repr) -> repr
