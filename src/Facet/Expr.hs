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
{-# LANGUAGE StandaloneDeriving #-}
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
, Sum(..)
, unSum
, Subset(..)
, inj
, prj
, Member
) where

import Control.Applicative ((<|>))
import Control.Lens (Prism', preview, prism', review)
import Data.Kind (Type)
import Data.Functor.Sum

class Expr (repr :: (Type -> Type) -> (Type -> Type)) where
  lam :: (Either (repr sig a) (Eff eff (repr eff a)) -> repr sig b) -> repr sig (repr eff a -> repr sig b)
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

  alg :: Eff sig (repr sig a) -> repr sig a

var :: Either (repr (sig :: Type -> Type) a) (None (repr sig' a)) -> repr sig a
var = \case
  Left  a -> a
  Right e -> absurd e

lam0 :: Expr repr => (repr sig a -> repr sig b) -> repr sig (repr sig a -> repr sig b)
lam0 f = lam (f . either id alg)

lam1 :: Expr repr => (Either (repr sig a) (Eff eff (repr eff a)) -> repr sig b) -> repr sig (repr eff a -> repr sig b)
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


send :: (Subset eff sig, Expr repr) => eff (repr sig a) -> repr sig a
send e = alg $ Eff (inj e) id


-- Effects

data State s k where
  Get :: State s s
  Put :: s -> State s ()

data Empty k = Empty


-- Examples

id' :: Expr repr => repr sig (repr sig a -> repr sig a)
id' = lam0 id

const' :: Expr repr => repr sig (repr sig a -> repr sig (repr sig b -> repr sig a))
const' = lam0 (lam0 . const)

flip' :: Expr repr => repr sig (repr sig (repr sig a -> repr sig (repr sig b -> repr sig c)) -> repr sig (repr sig b -> repr sig (repr sig a -> repr sig c)))
flip' = lam0 (\ f -> lam0 (\ b -> lam0 (\ a -> f $$ a $$ b)))

curry' :: Expr repr => repr sig (repr sig (repr sig (a, b) -> repr sig c) -> repr sig (repr sig a -> repr sig (repr sig b -> repr sig c)))
curry' = lam0 $ \ f -> lam0 $ \ a -> lam0 $ \ b -> f $$ inlr a b

uncurry' :: Expr repr => repr sig (repr sig (repr sig a -> repr sig (repr sig b -> repr sig c)) -> repr sig (repr sig (a, b) -> repr sig c))
uncurry' = lam0 $ \ f -> lam0 $ \ ab -> f $$ exl ab $$ exr ab

get :: (Expr repr, Member (State (repr sig s)) sig) => repr sig s
get = send (Eff Get id)

put :: (Expr repr, Member (State (repr sig s)) sig) => repr sig (repr sig s -> repr sig ())
put = lam0 $ \ s -> send (Eff (Put s) (const unit))

runState :: Expr repr => repr sig (repr sig s -> repr sig (repr (State (repr sig s)) a -> repr sig (s, a)))
runState = lam0 $ \ s -> lam1 $ \case
  Left a                 -> inlr s a
  Right (Eff Get     k) -> runState $$ s $$ k s
  Right (Eff (Put s) k) -> runState $$ s $$ k ()

execState :: Expr repr => repr sig (repr sig s -> repr sig (repr (State (repr sig s)) a -> repr sig a))
execState = lam0 $ \ s -> lam1 $ \case
  Left a                 -> a
  Right (Eff Get     k) -> execState $$ s $$ k s
  Right (Eff (Put s) k) -> execState $$ s $$ k ()


postIncr :: forall repr sig . (Expr repr, Num (repr sig Int), Member (State (repr sig Int)) sig) => repr sig Int
postIncr = get <& (put $$ (get + (1 :: repr sig Int)))


empty :: (Expr repr, Member Empty sig) => repr sig a
empty = send (Eff Empty id)

runEmpty :: Expr repr => repr sig (repr sig a -> repr sig (repr Empty a -> repr sig a))
runEmpty = lam0 $ \ a -> lam1 $ \case
  Left x              -> x
  Right (Eff Empty _) -> a

execEmpty :: Expr repr => repr sig (repr Empty a -> repr sig Bool)
execEmpty = lam1 (either (const true) (const false))


-- Signatures

data None a
  deriving (Functor)

absurd :: None a -> b
absurd = \case{}

data Eff f a where
  Eff :: f k -> (k -> a) -> Eff f a

deriving instance Functor (Eff f)

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

-- FIXME: should this be generalized to @Coercible eff1 eff2@?
instance Subset eff eff where
  sub = prism' id Just

instance Subset (Eff eff) (Sum (Eff eff) set) where
  sub = prism' InL (unSum Just (const Nothing))

instance Subset eff (Sum set1 (Sum set2 set3)) => Subset eff (Sum (Sum set1 set2) set3) where
  sub = prism' reassocL reassocR
    where
    reassocL = unSum (InL . InL) (unSum (InL . InR) InR) . inj
    reassocR = prj . unSum (unSum InL (InR . InL)) (InR . InR)

instance (Subset setl sets, Subset setr sets) => Subset (Sum setl setr) sets where
  sub = prism' (unSum inj inj) (\ s -> InL <$> prj s <|> InR <$> prj s)


type Member eff sig = Subset (Eff eff) sig
