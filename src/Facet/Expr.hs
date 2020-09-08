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
  inlr :: repr a -> repr b -> repr (a, b)
  fst' :: repr (a, b) -> repr a
  snd' :: repr (a, b) -> repr b

first :: (Expr repr, Pair repr) => repr (a -> a') -> repr (a, b) -> repr (a', b)
first f ab = inlr (f $$ fst' ab) (snd' ab)

second :: (Expr repr, Pair repr) => repr (b -> b') -> repr (a, b) -> repr (a, b')
second f ab = inlr (fst' ab) (f $$ snd' ab)


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

runState :: (Expr repr, Pair repr) => repr (s -> a -> (s, a))
runState = lam $ \ s -> lam $ \case
  Val a -> inlr (var s) a
  Eff (Get k) -> runState $$ var s $$ k (var s)
  Eff (Put s k) -> runState $$ s $$ k

execState :: Expr repr => repr (s -> a -> a)
execState = lam $ \ s -> lam $ \case
  Val a -> a
  Eff (Get k) -> execState $$ var s $$ k (var s)
  Eff (Put s k) -> execState $$ s $$ k


-- Signatures

class Has eff sig where
  inj :: eff a -> sig a

instance Has eff eff where
  inj = id

instance Has eff (Sum eff sig) where
  inj = L

instance Has eff sig => Has eff (Sum non sig) where
  inj = R . inj
