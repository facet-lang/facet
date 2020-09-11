{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Expr
( Expr(..)
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
, unSig2
, Subset(..)
, inj
, prj
, Member
, HFunctor(..)
) where

import Control.Applicative ((<|>))
import Control.Lens (Prism', preview, prism', review)
import Data.Kind (Type)

class Expr (repr :: Bin (Type -> Type) -> (Type -> Type)) where
  lam :: Subset eff sig' => (Either (repr sig a) (Sig eff (repr sig' a)) -> repr sig b) -> repr sig (repr sig' a -> repr sig b)
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

  alg :: Sig sig (repr sig a) -> repr sig a

  weaken :: Subset sub sup => repr sub a -> repr sup a

var :: Either (repr (sig :: Bin (Type -> Type)) a) (Sig 'B0 (repr sig' a)) -> repr sig a
var = \case
  Left  a -> a
  Right e -> unSig0 e

lam0 :: Expr repr => (repr sig a -> repr sig b) -> repr sig (repr sig a -> repr sig b)
lam0 f = lam (f . var)

lam1 :: (Expr repr, Subset ('B1 eff) sig') => (Either (repr sig a) (Sig ('B1 eff) (repr sig' a)) -> repr sig b) -> repr sig (repr sig' a -> repr sig b)
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


send :: (Subset eff sig, Expr repr) => Sig eff (repr sig a) -> repr sig a
send = alg . inj


-- Effects

data State s k
  = Get (s -> k)
  | Put s k
  deriving (Functor)


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

get :: (Expr repr, Member (State (repr sig s)) sig) => repr sig s
get = send (Sig1 (Get id))

put :: (Expr repr, Member (State (repr sig s)) sig) => repr sig (repr sig s -> repr sig ())
put = lam $ \ s -> send (Sig1 (Put (var s) unit))

runState :: Expr repr => repr sig (repr sig s -> repr sig (repr ('B1 (State (repr sig s))) a -> repr sig (s, a)))
runState = lam0 $ \ s -> lam1 $ \case
  Left a                 -> inlr s a
  Right (Sig1 (Get   k)) -> runState $$ s $$ k s
  Right (Sig1 (Put s k)) -> runState $$ s $$ k

execState :: Expr repr => repr sig (repr sig s -> repr sig (repr ('B1 (State (repr sig s))) a -> repr sig a))
execState = lam0 $ \ s -> lam1 $ \case
  Left a                 -> a
  Right (Sig1 (Get   k)) -> execState $$ s $$ k s
  Right (Sig1 (Put s k)) -> execState $$ s $$ k


postIncr :: forall repr sig . (Expr repr, Num (repr sig Int), Member (State (repr sig Int)) sig) => repr sig Int
postIncr = get <& (put $$ (get + (1 :: repr sig Int)))


-- Signatures

data Bin a
  = B0
  | B1 a
  | B2 (Bin a) (Bin a)

data Sig (sig :: Bin (Type -> Type)) k where
  Sig1 ::     f k -> Sig ('B1 f)   k
  SigL :: Sig l k -> Sig ('B2 l r) k
  SigR :: Sig r k -> Sig ('B2 l r) k

instance Functor f => Functor (Sig ('B1 f)) where
  fmap f (Sig1 a) = Sig1 (fmap f a)

instance (Functor (Sig l), Functor (Sig r)) => Functor (Sig ('B2 l r)) where
  fmap f = \case
    SigL l -> SigL (fmap f l)
    SigR r -> SigR (fmap f r)

unSig0 :: Sig 'B0 a -> b
unSig0 = \case{}

unSig2 :: (Sig l k -> a) -> (Sig r k -> a) -> (Sig ('B2 l r) k -> a)
unSig2 el er = \case
  SigL l -> el l
  SigR r -> er r


class Subset (sub :: Bin (Type -> Type)) (sup :: Bin (Type -> Type)) where
  sub :: Prism' (Sig sup a) (Sig sub a)

inj :: Subset sub sup => Sig sub a -> Sig sup a
inj = review sub

prj :: Subset sub sup => Sig sup a -> Maybe (Sig sub a)
prj = preview sub

instance Subset 'B0 sig where
  sub = prism' unSig0 (const Nothing)

-- FIXME: should this be generalized to @Coercible eff1 eff2@?
instance (eff1 ~ eff2) => Subset ('B1 eff1) ('B1 eff2) where
  sub = prism' id Just

instance Subset ('B1 eff) ('B2 ('B1 eff) set) where
  sub = prism' SigL (unSig2 Just (const Nothing))

instance Subset ('B1 eff) ('B2 set1 ('B2 set2 set3)) => Subset ('B1 eff) ('B2 ('B2 set1 set2) set3) where
  sub = prism' reassocL reassocR
    where
    reassocL = unSig2 (SigL . SigL) (unSig2 (SigL . SigR) SigR) . inj
    reassocR = prj . unSig2 (unSig2 SigL (SigR . SigL)) (SigR . SigR)

instance (Subset setl sets, Subset setr sets) => Subset ('B2 setl setr) sets where
  sub = prism' (unSig2 inj inj) (\ s -> SigL <$> prj s <|> SigR <$> prj s)


type Member eff sig = Subset ('B1 eff) sig


class HFunctor h where
  hmap :: (forall x . f x -> g x) -> h f a -> h g a
