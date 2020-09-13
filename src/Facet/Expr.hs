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
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Expr
( Expr(..)
, lam0
, lam1
, (<&)
, (&>)
, send
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
, None
, absurd
, Eff(..)
, absurdE
, Sum(..)
, unSum
, Subset(..)
, inj
, prj
, Member
) where

import Control.Applicative ((<|>))
import Control.Lens (Prism', preview, prism', review)
import Data.Bifunctor (first)
import Data.Kind (Type)
import Data.Functor.Sum

class (forall sig . Applicative (repr sig)) => Expr (repr :: (Type -> Type) -> (Type -> Type)) where
  -- | Values embed into computations at every signature.
  val :: repr None a -> repr sig a

  lam :: (Either (repr None a) (Eff eff (repr (Sum eff sig) a)) -> repr sig b) -> repr sig (repr (Sum eff sig) a -> repr sig b)
  ($$) :: repr sig (repr sig' a -> repr sig b) -> repr sig' a -> repr sig b
  infixl 9 $$

  inlr :: repr sig a -> repr sig b -> repr sig (a, b)
  exl :: repr sig (a, b) -> repr sig a
  exr :: repr sig (a, b) -> repr sig b

  inl :: repr sig a -> repr sig (Either a b)
  inr :: repr sig b -> repr sig (Either a b)
  exlr :: (repr sig a -> repr sig c) -> (repr sig b -> repr sig c) -> (repr sig (Either a b) -> repr sig c)

  true, false :: repr sig Bool
  iff :: repr sig Bool -> repr sig a -> repr sig a -> repr sig a

  alg :: Eff sig (repr sig a) -> repr sig a

  weaken :: repr sig a -> repr (Sum eff sig) a

-- FIXME: should lam0 & lam1 be primitive instead of lam?
lam0 :: Expr repr => (repr None a -> repr sig b) -> repr sig (repr sig a -> repr sig b)
lam0 f = (. weaken) <$> lam (f . either id absurdE)

lam1 :: Expr repr => (Either (repr sig a) (Eff eff (repr (Sum eff sig) a)) -> repr sig b) -> repr sig (repr (Sum eff sig) a -> repr sig b)
lam1 f = lam (f . first val)


(<&) :: Expr repr => repr sig a -> repr sig b -> repr sig a
a <& b = const' $$ a $$ b

(&>) :: Expr repr => repr sig a -> repr sig b -> repr sig b
a &> b = flip' $$ const' $$ a $$ b

infixl 1 <&, &>


send :: (Subset eff sig, Expr repr) => eff (repr sig a) -> repr sig a
send e = alg $ Eff (inj e) id


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
curry' = lam0 $ \ f -> lam0 $ \ a -> lam0 $ \ b -> val f $$ inlr (val a) (val b)

uncurry' :: Expr repr => repr sig (repr sig (repr sig a -> repr sig (repr sig b -> repr sig c)) -> repr sig (repr sig (a, b) -> repr sig c))
uncurry' = lam0 $ \ f -> lam0 $ \ ab -> val f $$ exl (val ab) $$ exr (val ab)

get :: (Expr repr, Member (State (repr None s)) sig) => repr sig s
get = alg $ Eff (inj Get) val

put :: (Expr repr, Member (State (repr None s)) sig) => repr sig (repr sig s -> repr sig ())
put = lam0 $ \ s -> alg (Eff (inj (Put s)) pure)

runState :: Expr repr => repr sig (repr sig s -> repr sig (repr (Sum (State (repr None s)) sig) a -> repr sig (s, a)))
runState = lam0 $ \ s -> lam1 $ \case
  Left a                -> inlr (val s) a
  Right (Eff Get     k) -> runState $$ val s $$ k s
  Right (Eff (Put s) k) -> runState $$ val s $$ k ()

execState :: Expr repr => repr sig (repr sig s -> repr sig (repr (Sum (State (repr None s)) sig) a -> repr sig a))
execState = lam0 $ \ s -> lam1 $ \case
  Left a                -> a
  Right (Eff Get     k) -> execState $$ val s $$ k s
  Right (Eff (Put s) k) -> execState $$ val s $$ k ()


postIncr :: forall repr sig . (Expr repr, Num (repr sig Int), Member (State (repr None Int)) sig) => repr sig Int
postIncr = get <& put $$ (get + 1 :: repr sig Int)


empty :: (Expr repr, Member Empty sig) => repr sig a
empty = send Empty

runEmpty :: Expr repr => repr sig (repr sig a -> repr sig (repr (Sum Empty sig) a -> repr sig a))
runEmpty = lam0 $ \ a -> lam1 $ \case
  Left x              -> x
  Right (Eff Empty _) -> val a

execEmpty :: Expr repr => repr sig (repr (Sum Empty sig) a -> repr sig Bool)
execEmpty = lam1 (either (const true) (const false))


-- Signatures

data None a
  deriving (Functor)

absurd :: None a -> b
absurd = \case{}

data Eff f a where
  Eff :: f k -> (k -> a) -> Eff f a

deriving instance Functor (Eff f)

absurdE :: Eff None a -> b
absurdE (Eff e _) = absurd e

unSum :: (l a -> b) -> (r a -> b) -> Sum l r a -> b
unSum fl fr = \case
  InL l -> fl l
  InR r -> fr r


class Subset (sub :: Type -> Type) (sup :: Type -> Type) where
  sub :: Prism' (sup a) (sub a)

inj :: Subset sub sup => sub a -> sup a
inj = review sub

prj :: Subset sub sup => sup a -> Maybe (sub a)
prj = preview sub

instance Subset None sig where
  sub = prism' absurd (const Nothing)

instance Subset eff eff where
  sub = prism' id Just

instance Subset eff (Sum eff set) where
  sub = prism' InL (unSum Just (const Nothing))

instance Subset eff (Sum set1 (Sum set2 set3)) => Subset eff (Sum (Sum set1 set2) set3) where
  sub = prism' reassocL reassocR
    where
    reassocL = unSum (InL . InL) (unSum (InL . InR) InR) . inj
    reassocR = prj . unSum (unSum InL (InR . InL)) (InR . InR)

instance (Subset setl sets, Subset setr sets) => Subset (Sum setl setr) sets where
  sub = prism' (unSum inj inj) (\ s -> InL <$> prj s <|> InR <$> prj s)


type Member eff sig = Subset eff sig
