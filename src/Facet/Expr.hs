{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
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
, lam1
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
, Bin(..)
, Sig(..)
, unSig0
, unSig1
, unSig2
, Subset(..)
, Member
) where

import Data.Kind (Type)

class Expr (repr :: Bin ((Type -> Type) -> (Type -> Type)) -> (Type -> Type)) where
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

  alg :: Sig sig (repr sig) (repr sig a) -> repr sig a

data Comp (eff :: Bin ((Type -> Type) -> (Type -> Type))) (repr :: Bin ((Type -> Type) -> (Type -> Type)) -> (Type -> Type)) sig sig' a where
  Val :: repr sig a -> Comp eff repr sig sig' a
  Eff :: Sig eff (repr sig) k -> (k -> repr sig' a) -> Comp eff repr sig sig' a

var :: Comp 'B0 repr sig sig' a -> repr sig a
var = \case
  Val a   -> a
  Eff e _ -> unSig0 e

lam0 :: Expr repr => (repr sig a -> repr sig b) -> repr sig (repr sig a -> repr sig b)
lam0 f = lam (f . var)

lam1 :: (Expr repr, Subset ('B1 eff) sig') => (Comp ('B1 eff) repr sig sig' a -> repr sig b) -> repr sig (repr sig' a -> repr sig b)
lam1 = lam


(<&) :: Expr repr => repr sig a -> repr sig b -> repr sig a
a <& b = const' $$ a $$ b

(&>) :: Expr repr => repr sig a -> repr sig b -> repr sig b
a &> b = flip' $$ const' $$ a $$ b

infixl 1 <&, &>


first :: Expr repr => repr sig (repr sig a -> repr sig a') -> repr sig (a, b) -> repr sig (a', b)
first f ab = inlr (f $$ exl ab) (exr ab)

second :: Expr repr => repr sig (repr sig b -> repr sig b') -> repr sig (a, b) -> repr sig (a, b')
second f ab = inlr (exl ab) (f $$ exr ab)


send :: (Subset eff sig, Expr repr) => Sig eff (repr sig) (repr sig a) -> repr sig a
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
get = send (Sig1 Get)

put :: (Expr repr, Member (State s) sig) => repr sig (repr sig s -> repr sig ())
put = lam $ \ s -> send (Sig1 (Put (var s)))

runState :: Expr repr => repr sig (repr sig s -> repr sig (repr ('B1 (State s)) a -> repr sig (s, a)))
runState = lam0 $ \ s -> lam1 $ \case
  Val a                -> inlr s a
  Eff (Sig1 Get)     k -> runState $$ s $$ k s
  Eff (Sig1 (Put s)) k -> runState $$ s $$ k unit

execState :: Expr repr => repr sig (repr sig s -> repr sig (repr ('B1 (State s)) a -> repr sig a))
execState = lam0 $ \ s -> lam1 $ \case
  Val a                -> a
  Eff (Sig1 Get)     k -> execState $$ s $$ k s
  Eff (Sig1 (Put s)) k -> execState $$ s $$ k unit


postIncr :: forall repr sig . (Expr repr, Num (repr sig Int), Member (State Int) sig) => repr sig Int
postIncr = get <& (put $$ (get + (1 :: repr sig Int)))


-- Signatures

data Bin a
  = B0
  | B1 a
  | B2 (Bin a) (Bin a)

data Sig (sig :: Bin ((Type -> Type) -> (Type -> Type))) (repr :: Type -> Type) k where
  Sig1 ::     f repr k -> Sig ('B1 f)   repr k
  SigL :: Sig l repr k -> Sig ('B2 l r) repr k
  SigR :: Sig r repr k -> Sig ('B2 l r) repr k

unSig0 :: Sig 'B0 repr a -> b
unSig0 = \case{}

unSig1 :: Sig ('B1 f) repr k -> f repr k
unSig1 (Sig1 f) = f

unSig2 :: (Sig l repr k -> a) -> (Sig r repr k -> a) -> (Sig ('B2 l r) repr k -> a)
unSig2 el er = \case
  SigL l -> el l
  SigR r -> er r


class Subset (sub :: Bin ((Type -> Type) -> (Type -> Type))) (sup :: Bin ((Type -> Type) -> (Type -> Type))) where
  inj :: Sig sub repr a -> Sig sup repr a

instance Subset 'B0 sig where
  inj = unSig0

-- FIXME: should this be generalized to @Coercible eff1 eff2@?
instance (eff1 ~ eff2) => Subset ('B1 eff1) ('B1 eff2) where
  inj = id

instance Subset ('B1 eff) ('B2 ('B1 eff) set) where
  inj = SigL

instance Subset ('B1 eff) ('B2 set1 ('B2 set2 set3)) => Subset ('B1 eff) ('B2 ('B2 set1 set2) set3) where
  inj = unSig2 (SigL . SigL) (unSig2 (SigL . SigR) SigR) . inj

instance (Subset setl sets, Subset setr sets) => Subset ('B2 setl setr) sets where
  inj = unSig2 inj inj


type Member eff sig = Subset ('B1 eff) sig
