{-# LANGUAGE EmptyCase #-}
module Facet.Expr
( Expr(..)
, Inst(..)
, var
  -- * Effects
, Sum(..)
, State(..)
, None
  -- * Examples
, id'
, const'
) where

class Expr repr where
  lam :: [Inst eff (repr a) -> repr b] -> repr (a -> b)
  ($$) :: repr (a -> b) -> repr a -> repr b
  infixl 9 $$


data Inst eff a
  = Val a
  | Eff (eff a)

var :: Inst None a -> a
var (Val a) = a
var (Eff e) = case e of {}


-- Effects

-- | Sum of effects represented as a binary tree.
data Sum l r k
  = L (l k)
  | R (r k)

data State s k
  = Get (s -> k)
  | Put s k

-- | No effects.
data None k


-- Examples

id' :: Expr repr => repr (a -> a)
id' = lam [var]

const' :: Expr repr => repr (a -> b -> a)
const' = lam [\ a -> lam [const (var a)]]
