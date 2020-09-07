module Facet.Expr
( Expr(..)
  -- * Effects
, State(..)
  -- * Examples
, id'
, const'
) where

class Expr repr where
  lam :: [repr a -> repr b] -> repr (a -> b)
  ($$) :: repr (a -> b) -> repr a -> repr b
  infixl 9 $$


-- Effects

data State s m k
  = Get (s -> m k)
  | Put s (m k)


-- Examples

id' :: Expr repr => repr (a -> a)
id' = lam [id]

const' :: Expr repr => repr (a -> b -> a)
const' = lam [\ a -> lam [const a]]
