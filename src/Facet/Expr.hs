{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Expr
( Expr(..)
, var
, (<&)
, (&>)
, Unit(..)
, Pair(..)
, first
, second
, Eff(..)
, send
  -- * Effects
, State(..)
, Return(..)
  -- * Examples
, id'
, const'
, flip'
, curry'
, uncurry'
, get
, put
, runState
, execState
, execState'
  -- * Signatures
, S2(..)
, S1(..)
, S0
, absurd
, Subset(..)
) where

import Data.Kind (Type)

class Expr (repr :: ((Type -> Type) -> (Type -> Type)) -> (Type -> Type)) where
  lam :: (Either (repr sig a) (eff (repr sig) (repr sig' a)) -> repr sig b) -> repr sig (repr sig' a -> repr sig b)
  ($$) :: repr sig (repr sig' a -> repr sig b) -> repr sig' a -> repr sig b
  infixl 9 $$

var :: Either a (S0 f b) -> a
var = either id absurd


(<&) :: Expr repr => repr sig a -> repr sig b -> repr sig a
a <& b = const' $$ a $$ b

(&>) :: Expr repr => repr sig a -> repr sig b -> repr sig b
a &> b = flip' $$ const' $$ a $$ b

infixl 1 <&, &>


class Unit (repr :: ((Type -> Type) -> (Type -> Type)) -> (Type -> Type)) where
  unit :: repr sig ()


class Pair (repr :: ((Type -> Type) -> (Type -> Type)) -> (Type -> Type)) where
  inlr :: repr sig a -> repr sig b -> repr sig (a, b)
  exl :: repr sig (a, b) -> repr sig a
  exr :: repr sig (a, b) -> repr sig b

first :: (Expr repr, Pair repr) => repr sig (repr sig a -> repr sig a') -> repr sig (a, b) -> repr sig (a', b)
first f ab = inlr (f $$ exl ab) (exr ab)

second :: (Expr repr, Pair repr) => repr sig (repr sig b -> repr sig b') -> repr sig (a, b) -> repr sig (a, b')
second f ab = inlr (exl ab) (f $$ exr ab)


class Eff repr where
  alg :: sig (repr sig) (repr sig a) -> repr sig a

send :: (Subset eff sig, Eff repr) => eff (repr sig) (repr sig a) -> repr sig a
send = alg . inj


-- Effects

data State s (repr :: Type -> Type) k
  = Get (repr s -> k)
  | Put (repr s) k

-- | The identity effect.
newtype Return (repr :: Type -> Type) a = Return (repr a)


-- Examples

id' :: Expr repr => repr sig (repr sig a -> repr sig a)
id' = lam var

const' :: Expr repr => repr sig (repr sig a -> repr sig (repr sig b -> repr sig a))
const' = lam (lam . const . var)

flip' :: Expr repr => repr sig (repr sig (repr sig a -> repr sig (repr sig b -> repr sig c)) -> repr sig (repr sig b -> repr sig (repr sig a -> repr sig c)))
flip' = lam (\ f -> lam (\ b -> lam (\ a -> var f $$ var a $$ var b)))

curry' :: (Expr repr, Pair repr) => repr sig (repr sig (repr sig (a, b) -> repr sig c) -> repr sig (repr sig a -> repr sig (repr sig b -> repr sig c)))
curry' = lam $ \ f -> lam $ \ a -> lam $ \ b -> var f $$ inlr (var a) (var b)

uncurry' :: (Expr repr, Pair repr) => repr sig (repr sig (repr sig a -> repr sig (repr sig b -> repr sig c)) -> repr sig (repr sig (a, b) -> repr sig c))
uncurry' = lam $ \ f -> lam $ \ ab -> var f $$ exl (var ab) $$ exr (var ab)

get :: (Eff repr, Subset (State s) sig) => repr sig s
get = send (Get id)

put :: (Eff repr, Expr repr, Unit repr, Subset (State s) sig) => repr sig (repr sig s -> repr sig ())
put = lam $ \ s -> send (Put (var s) unit)

runState :: (Expr repr, Pair repr) => repr sig (repr sig s -> repr sig (repr (State s) a -> repr sig (s, a)))
runState = lam $ \ s -> lam $ \case
  Left a          -> inlr (var s) a
  Right (Get   k) -> runState $$ var s $$ k (var s)
  Right (Put s k) -> runState $$ s $$ k

execState :: Expr repr => repr sig (repr sig s -> repr sig (repr (State s) a -> repr sig a))
execState = lam $ \ s -> lam $ \case
  Left a          -> a
  Right (Get   k) -> execState $$ var s $$ k (var s)
  Right (Put s k) -> execState $$ s $$ k

execState' :: Expr repr => repr sig s -> repr (State s) a -> repr sig a
execState' s a = lam (\case
  Left a          -> a
  Right (Get   k) -> execState' s (k s)
  Right (Put s k) -> execState' s k) $$ a


-- Signatures

-- | Union of effect signature, represented as a binary tree.
data S2 l r (repr :: Type -> Type) k
  = SL (l repr k)
  | SR (r repr k)

newtype S1 eff (repr :: Type -> Type) k = S1 (eff repr k)

-- | No effects.
data S0 (repr :: Type -> Type) k

absurd :: S0 repr a -> b
absurd = \case{}


class Subset (sub :: (Type -> Type) -> (Type -> Type)) (sup :: (Type -> Type) -> (Type -> Type)) where
  inj :: sub repr a -> sup repr a

instance Subset S0 S0 where
  inj = absurd

instance Subset S0 (S1 eff) where
  inj = absurd

instance Subset S0 (S2 l r) where
  inj = absurd

instance (eff1 ~ eff2) => Subset (S1 eff1) (S1 eff2) where
  inj = id

instance (eff1 ~ eff2) => Subset (S1 eff1) (S2 (S1 eff2) set) where
  inj = SL

instance (Subset setl sets, Subset setr sets) => Subset (S2 setl setr) sets where
  inj (SL setl) = inj setl
  inj (SR setr) = inj setr
