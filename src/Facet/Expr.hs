{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Expr
( Expr(..)
, Inst(..)
, var
, Pair(..)
, first
, second
  -- * Effects
, Sum(..)
, State(..)
, None
  -- * Examples
, id'
, const'
, flip'
, execState
) where

class Expr repr where
  lam :: (Inst eff (repr a) -> repr b) -> repr (a -> b)
  ($$) :: repr (a -> b) -> repr a -> repr b
  infixl 9 $$


data Inst eff a
  = Val a
  | Eff (eff a)

var :: Inst None a -> a
var (Val a) = a
var (Eff e) = case e of {}


class Pair repr where
  pair :: repr a -> repr b -> repr (a, b)
  fst' :: repr (a, b) -> repr a
  snd' :: repr (a, b) -> repr b

first :: (Expr repr, Pair repr) => repr (a -> a') -> repr (a, b) -> repr (a', b)
first f ab = pair (f $$ fst' ab) (snd' ab)

second :: (Expr repr, Pair repr) => repr (b -> b') -> repr (a, b) -> repr (a, b')
second f ab = pair (fst' ab) (f $$ snd' ab)


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
id' = lam var

const' :: Expr repr => repr (a -> b -> a)
const' = lam (lam . const . var)

flip' :: Expr repr => repr ((a -> b -> c) -> (b -> a -> c))
flip' = lam (\ f -> lam (\ b -> lam (\ a -> var f $$ var a $$ var b)))

execState :: Expr repr => repr (a -> s -> a)
-- FIXME: this is using a carrier type of @a@ but it should be using @s -> (s, a)@ or something like that.
execState = lam (\case
  Val a -> lam (const a)
  Eff (Get k) -> lam (k . var)
  -- FIXME: how exactly do we use the new state?
  Eff (Put _ k) -> lam (const k))
