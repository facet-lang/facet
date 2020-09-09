{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Expr
( Expr(..)
, var
, lam0
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
  -- * Signatures
, S2(..)
, unS2
, S1(..)
, S0
, unS0
, Subset(..)
, Member
) where

import Data.Kind (Type)

class Expr (repr :: ((Type -> Type) -> (Type -> Type)) -> (Type -> Type)) where
  lam :: Subset eff sig' => (Either (repr sig a) (eff (repr sig) (repr sig' a)) -> repr sig b) -> repr sig (repr sig' a -> repr sig b)
  ($$) :: repr sig (repr sig' a -> repr sig b) -> repr sig' a -> repr sig b
  infixl 9 $$

var :: Either (repr (sig :: (Type -> Type) -> (Type -> Type)) a) (S0 (repr sig) (repr sig a)) -> repr sig a
var = either id unS0

lam0 :: Expr repr => (repr sig a -> repr sig b) -> repr sig (repr sig a -> repr sig b)
lam0 f = lam (f . var)


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
const' = lam (lam0 . const . var)

flip' :: Expr repr => repr sig (repr sig (repr sig a -> repr sig (repr sig b -> repr sig c)) -> repr sig (repr sig b -> repr sig (repr sig a -> repr sig c)))
flip' = lam (\ f -> lam (\ b -> lam (\ a -> var f $$ var a $$ var b)))

curry' :: (Expr repr, Pair repr) => repr sig (repr sig (repr sig (a, b) -> repr sig c) -> repr sig (repr sig a -> repr sig (repr sig b -> repr sig c)))
curry' = lam $ \ f -> lam $ \ a -> lam $ \ b -> var f $$ inlr (var a) (var b)

uncurry' :: (Expr repr, Pair repr) => repr sig (repr sig (repr sig a -> repr sig (repr sig b -> repr sig c)) -> repr sig (repr sig (a, b) -> repr sig c))
uncurry' = lam $ \ f -> lam $ \ ab -> var f $$ exl (var ab) $$ exr (var ab)

get :: (Eff repr, Member (State s) sig) => repr sig s
get = send (S1 (Get id))

put :: (Eff repr, Expr repr, Unit repr, Member (State s) sig) => repr sig (repr sig s -> repr sig ())
put = lam $ \ s -> send (S1 (Put (var s) unit))

runState :: (Expr repr, Pair repr) => repr sig (repr sig s -> repr sig (repr (S1 (State s)) a -> repr sig (s, a)))
runState = lam $ \ s -> lam $ \case
  Left a               -> inlr (var s) a
  Right (S1 (Get   k)) -> runState $$ var s $$ k (var s)
  Right (S1 (Put s k)) -> runState $$ s $$ k

execState :: Expr repr => repr sig (repr sig s -> repr sig (repr (S1 (State s)) a -> repr sig a))
execState = lam $ \ s -> lam $ \case
  Left a               -> a
  Right (S1 (Get   k)) -> execState $$ var s $$ k (var s)
  Right (S1 (Put s k)) -> execState $$ s $$ k


-- Signatures

-- | Union of effect signature, represented as a binary tree.
data S2 l r (repr :: Type -> Type) k
  = SL (l repr k)
  | SR (r repr k)

unS2 :: (l repr k -> a) -> (r repr k -> a) -> (S2 l r repr k -> a)
unS2 el er = \case
  SL l -> el l
  SR r -> er r

newtype S1 eff (repr :: Type -> Type) k = S1 { unS1 :: eff repr k }

-- | No effects.
data S0 (repr :: Type -> Type) k

unS0 :: S0 repr a -> b
unS0 = \case{}


class Subset (sub :: (Type -> Type) -> (Type -> Type)) (sup :: (Type -> Type) -> (Type -> Type)) where
  inj :: sub repr a -> sup repr a

instance Subset S0 sig where
  inj = unS0

-- FIXME: should this be generalized to @Coercible eff1 eff2@?
instance (eff1 ~ eff2) => Subset (S1 eff1) (S1 eff2) where
  inj = id

instance Subset (S1 eff) (S2 (S1 eff) set) where
  inj = SL

instance Subset (S1 eff) (S2 set1 (S2 set2 set3)) => Subset (S1 eff) (S2 (S2 set1 set2) set3) where
  inj = reassoc . inj
    where
    reassoc = \case
      SL l      -> SL (SL l)
      SR (SL l) -> SL (SR l)
      SR (SR r) -> SR r

instance (Subset setl sets, Subset setr sets) => Subset (S2 setl setr) sets where
  inj (SL setl) = inj setl
  inj (SR setr) = inj setr


type Member eff sig = Subset (S1 eff) sig
