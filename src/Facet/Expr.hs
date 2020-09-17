{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
module Facet.Expr
( Expr(..)
, Inst(..)
, absurdI
, lam0
, lam1
, (<&)
, (&>)
, lam1'
  -- * Effects
, State(..)
, Empty(..)
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
, empty
, runEmpty
, execEmpty
  -- * Signatures
, module Facet.Signature
) where

import Data.Bifunctor (first)
import Data.Functor.Sum
import Facet.Signature

class (forall sig . Applicative (repr sig)) => Expr repr where
  -- FIXME: patterns
  lam :: (Either (repr None a) (Inst eff (repr (Sum eff sig) a)) -> repr sig b) -> repr sig (repr (Sum eff sig) a -> repr sig b)
  ($$) :: repr sig (repr sig' a -> repr sig b) -> repr sig' a -> repr sig b
  infixl 9 $$

  alg :: sig k -> (k -> repr sig a) -> repr sig a

  weakenBy :: (forall x . sub x -> sup x) -> repr sub a -> repr sup a

  -- FIXME: constructors
  -- FIXME: patterns

data Inst eff a
  = forall k . Inst (eff k) (k -> a)

deriving instance Functor (Inst eff)

absurdI :: Inst None a -> b
absurdI (Inst e _) = absurd e


-- | Values embed into computations at every signature.
val :: Expr repr => repr None a -> repr sig a
val = weakenBy absurd

lam0 :: Expr repr => (repr None a -> repr sig b) -> repr sig (repr sig a -> repr sig b)
lam0 f = (. weakenBy InR) <$> lam (f . either id absurdI)

lam1 :: Expr repr => (Either (repr sig a) (Inst eff (repr (Sum eff sig) a)) -> repr sig b) -> repr sig (repr (Sum eff sig) a -> repr sig b)
lam1 f = lam (f . first val)


(<&) :: Expr repr => repr sig a -> repr sig b -> repr sig a
a <& b = const' $$ a $$ b

(&>) :: Expr repr => repr sig a -> repr sig b -> repr sig b
a &> b = flip' $$ const' $$ a $$ b

infixl 1 <&, &>

lam1' :: Expr repr => (Either (repr sig a) (Inst eff (repr (Sum eff sig) a)) -> repr sig b) -> repr sig (repr (Sum eff sig) a -> repr sig b)
lam1' f = lam1 $ \case
  Left  a -> f (Left a)
  Right i -> f (Right i)


-- Effects

data State s k where
  Get :: State s s
  Put :: s -> State s ()

data Empty k = Empty


-- Examples

id' :: Expr repr => repr sig (repr sig a -> repr sig a)
id' = lam0 val

const' :: Expr repr => repr sig (repr sig a -> repr sig (repr sig b -> repr sig a))
const' = lam0 (lam0 . const . val)

flip' :: Expr repr => repr sig (repr sig (repr sig a -> repr sig (repr sig b -> repr sig c)) -> repr sig (repr sig b -> repr sig (repr sig a -> repr sig c)))
flip' = lam0 (\ f -> lam0 (\ b -> lam0 (\ a -> val f $$ val a $$ val b)))

curry' :: Expr repr => repr sig (repr sig (repr sig (a, b) -> repr sig c) -> repr sig (repr sig a -> repr sig (repr sig b -> repr sig c)))
curry' = lam0 $ \ f -> lam0 $ \ a -> lam0 $ \ b -> val f $$ ((,) <$> val a <*> val b)

uncurry' :: Expr repr => repr sig (repr sig (repr sig a -> repr sig (repr sig b -> repr sig c)) -> repr sig (repr sig (a, b) -> repr sig c))
uncurry' = lam0 $ \ f -> lam0 $ \ ab -> val f $$ fmap fst (val ab) $$ fmap snd (val ab)

get :: (Expr repr, Member (State (repr None s)) sig) => repr sig s
get = alg (inj Get) val

put :: (Expr repr, Member (State (repr None s)) sig) => repr sig (repr sig s -> repr sig ())
put = lam0 $ \ s -> alg (inj (Put s)) pure

runState :: Expr repr => repr sig (repr sig s -> repr sig (repr (Sum (State (repr None s)) sig) a -> repr sig (s, a)))
runState = lam0 $ \ s -> lam1 $ \case
  Left a                -> (,) <$> val s <*> a
  Right (Inst Get     k) -> runState $$ val s $$ k s
  Right (Inst (Put s) k) -> runState $$ val s $$ k ()

execState :: Expr repr => repr sig (repr sig s -> repr sig (repr (Sum (State (repr None s)) sig) a -> repr sig a))
execState = lam0 $ \ s -> lam1 $ \case
  Left a                -> a
  Right (Inst Get     k) -> execState $$ val s $$ k s
  Right (Inst (Put s) k) -> execState $$ val s $$ k ()


postIncr :: forall repr sig . (Expr repr, Num (repr sig Int), Member (State (repr None Int)) sig) => repr sig Int
postIncr = get <& put $$ (get + 1 :: repr sig Int)


empty :: (Expr repr, Member Empty sig) => repr sig a
empty = alg (inj Empty) pure

runEmpty :: Expr repr => repr sig (repr sig a -> repr sig (repr (Sum Empty sig) a -> repr sig a))
runEmpty = lam0 $ \ a -> lam1 $ \case
  Left x               -> x
  Right (Inst Empty _) -> val a

execEmpty :: Expr repr => repr sig (repr (Sum Empty sig) a -> repr sig Bool)
execEmpty = lam1 (either (const (pure True)) (const (pure False)))
