{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Expr
( Expr(..)
, Comp(..)
, var
, lam0
, (<&)
, (&>)
, first
, second
, send
  -- * Effects
, State(..)
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
, postIncr
  -- * Signatures
, Sig(..)
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
  lam :: Subset eff sig' => (Comp eff repr sig sig' a -> repr sig b) -> repr sig (repr sig' a -> repr sig b)
  ($$) :: repr sig (repr sig' a -> repr sig b) -> repr sig' a -> repr sig b
  infixl 9 $$

  unit :: repr sig ()

  inlr :: repr sig a -> repr sig b -> repr sig (a, b)
  exl :: repr sig (a, b) -> repr sig a
  exr :: repr sig (a, b) -> repr sig b

  inl :: repr sig a -> repr sig (Either a b)
  inr :: repr sig b -> repr sig (Either a b)
  exlr :: (repr sig a -> repr sig c) -> (repr sig b -> repr sig c) -> (repr sig (Either a b) -> repr sig c)

  true, false :: repr sig Bool
  iff :: repr sig Bool -> repr sig a -> repr sig a -> repr sig a

  alg :: sig (repr sig) (repr sig a) -> repr sig a

data Comp eff (repr :: ((Type -> Type) -> (Type -> Type)) -> (Type -> Type)) sig sig' a where
  Val :: repr sig a -> Comp eff repr sig sig' a
  Eff :: eff (repr sig) k -> (k -> repr sig' a) -> Comp eff repr sig sig' a

var :: Comp S0 repr sig sig' a -> repr sig a
var = \case
  Val a   -> a
  Eff e _ -> unS0 e

lam0 :: Expr repr => (repr sig a -> repr sig b) -> repr sig (repr sig a -> repr sig b)
lam0 f = lam (f . var)


(<&) :: Expr repr => repr sig a -> repr sig b -> repr sig a
a <& b = const' $$ a $$ b

(&>) :: Expr repr => repr sig a -> repr sig b -> repr sig b
a &> b = flip' $$ const' $$ a $$ b

infixl 1 <&, &>


first :: Expr repr => repr sig (repr sig a -> repr sig a') -> repr sig (a, b) -> repr sig (a', b)
first f ab = inlr (f $$ exl ab) (exr ab)

second :: Expr repr => repr sig (repr sig b -> repr sig b') -> repr sig (a, b) -> repr sig (a, b')
second f ab = inlr (exl ab) (f $$ exr ab)


send :: (Subset eff sig, Expr repr) => eff (repr sig) (repr sig a) -> repr sig a
send = alg . inj


-- Effects

data State s (repr :: Type -> Type) k where
  Get :: State s repr (repr s)
  Put :: repr s -> State s repr (repr ())


-- Examples

id' :: Expr repr => repr sig (repr sig a -> repr sig a)
id' = lam var

const' :: Expr repr => repr sig (repr sig a -> repr sig (repr sig b -> repr sig a))
const' = lam (lam0 . const . var)

flip' :: Expr repr => repr sig (repr sig (repr sig a -> repr sig (repr sig b -> repr sig c)) -> repr sig (repr sig b -> repr sig (repr sig a -> repr sig c)))
flip' = lam (\ f -> lam (\ b -> lam (\ a -> var f $$ var a $$ var b)))

curry' :: Expr repr => repr sig (repr sig (repr sig (a, b) -> repr sig c) -> repr sig (repr sig a -> repr sig (repr sig b -> repr sig c)))
curry' = lam $ \ f -> lam $ \ a -> lam $ \ b -> var f $$ inlr (var a) (var b)

uncurry' :: Expr repr => repr sig (repr sig (repr sig a -> repr sig (repr sig b -> repr sig c)) -> repr sig (repr sig (a, b) -> repr sig c))
uncurry' = lam $ \ f -> lam $ \ ab -> var f $$ exl (var ab) $$ exr (var ab)

get :: (Expr repr, Member (State s) sig) => repr sig s
get = send (S1 Get)

put :: (Expr repr, Member (State s) sig) => repr sig (repr sig s -> repr sig ())
put = lam $ \ s -> send (S1 (Put (var s)))

runState :: Expr repr => repr sig (repr sig s -> repr sig (repr (S1 (State s)) a -> repr sig (s, a)))
runState = lam0 $ \ s -> lam $ \case
  Val a              -> inlr s a
  Eff (S1 Get)     k -> runState $$ s $$ k s
  Eff (S1 (Put s)) k -> runState $$ s $$ k unit

execState :: Expr repr => repr sig (repr sig s -> repr sig (repr (S1 (State s)) a -> repr sig a))
execState = lam0 $ \ s -> lam $ \case
  Val a              -> a
  Eff (S1 Get)     k -> execState $$ s $$ k s
  Eff (S1 (Put s)) k -> execState $$ s $$ k unit


postIncr :: forall repr sig . (Expr repr, Num (repr sig Int), Member (State Int) sig) => repr sig Int
postIncr = get <& (put $$ (get + (1 :: repr sig Int)))


-- Signatures

data Sig (repr :: Type -> Type) f k where
  Sig0 ::             Sig repr S0 k
  Sig1 :: f repr k -> Sig repr (S1 f) k
  SigL :: l repr k -> Sig repr (S2 l r) k
  SigR :: r repr k -> Sig repr (S2 l r) k

-- | Union of effect signatures, represented as a binary tree.
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
  inj = unS2 inj inj


type Member eff sig = Subset (S1 eff) sig
