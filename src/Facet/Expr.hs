{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Expr
( Expr(..)
, Inst(..)
, var
, (<&)
, (&>)
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
, runState
, execState
  -- * Signatures
, Has
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


(<&) :: Expr repr => repr a -> repr b -> repr a
a <& b = const' $$ a $$ b

(&>) :: Expr repr => repr a -> repr b -> repr b
a &> b = flip' $$ const' $$ a $$ b

infixl 1 <&, &>


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

runState :: (Expr repr, Pair repr) => repr (a -> s -> (s, a))
runState = lam $ \case
  Val a -> lam $ \ s -> pair (var s) a
  Eff (Get k) -> lam $ \ s -> pair (var s) (k (var s))
  Eff (Put s k) -> lam $ \ _ -> pair s k

execState :: (Expr repr, Pair repr) => repr (a -> s -> a)
execState = lam $ \ a -> lam $ \ s -> snd' (runState $$ var a $$ var s)


-- Signatures

class Has eff sig where
  inj :: eff a -> sig a

instance Has eff eff where
  inj = id

instance Has eff (Sum eff sig) where
  inj = L
