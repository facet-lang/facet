{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
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

class Expr (val :: Type -> Type) (comp :: (Type -> Type) -> (Type -> Type)) | comp -> val where
  -- | Values embed into computations at every signature.
  val :: val a -> comp sig a

  lam :: (Either (comp sig a) (Eff eff (comp eff a)) -> comp sig b) -> comp sig (comp eff a -> comp sig b)
  ($$) :: comp sig (comp sig' a -> comp sig b) -> comp sig' a -> comp sig b
  infixl 9 $$

  unit :: comp sig ()

  inlr :: comp sig a -> comp sig b -> comp sig (a, b)
  exl :: comp sig (a, b) -> comp sig a
  exr :: comp sig (a, b) -> comp sig b

  inl :: comp sig a -> comp sig (Either a b)
  inr :: comp sig b -> comp sig (Either a b)
  exlr :: (comp sig a -> comp sig c) -> (comp sig b -> comp sig c) -> (comp sig (Either a b) -> comp sig c)

  true, false :: comp sig Bool
  iff :: comp sig Bool -> comp sig a -> comp sig a -> comp sig a

  alg :: Eff sig (comp sig a) -> comp sig a

lam0 :: Expr val comp => (comp sig a -> comp sig b) -> comp sig (comp sig a -> comp sig b)
lam0 f = lam (f . either id alg)

lam1 :: Expr val comp => (Either (comp sig a) (Eff eff (comp eff a)) -> comp sig b) -> comp sig (comp eff a -> comp sig b)
lam1 = lam


(<&) :: Expr val comp => comp sig a -> comp sig b -> comp sig a
a <& b = const' $$ a $$ b

(&>) :: Expr val comp => comp sig a -> comp sig b -> comp sig b
a &> b = flip' $$ const' $$ a $$ b

infixl 1 <&, &>


first :: Expr val comp => comp sig (comp sig a -> comp sig a') -> comp sig (a, b) -> comp sig (a', b)
first f ab = inlr (f $$ exl ab) (exr ab)

second :: Expr val comp => comp sig (comp sig b -> comp sig b') -> comp sig (a, b) -> comp sig (a, b')
second f ab = inlr (exl ab) (f $$ exr ab)


send :: (Subset eff sig, Expr val comp) => eff (comp sig a) -> comp sig a
send e = alg $ Eff (inj e) id


-- Effects

data State s k where
  Get :: State s s
  Put :: s -> State s ()

data Empty k = Empty


-- Examples

id' :: Expr val comp => comp sig (comp sig a -> comp sig a)
id' = lam0 id

const' :: Expr val comp => comp sig (comp sig a -> comp sig (comp sig b -> comp sig a))
const' = lam0 (lam0 . const)

flip' :: Expr val comp => comp sig (comp sig (comp sig a -> comp sig (comp sig b -> comp sig c)) -> comp sig (comp sig b -> comp sig (comp sig a -> comp sig c)))
flip' = lam0 (\ f -> lam0 (\ b -> lam0 (\ a -> f $$ a $$ b)))

curry' :: Expr val comp => comp sig (comp sig (comp sig (a, b) -> comp sig c) -> comp sig (comp sig a -> comp sig (comp sig b -> comp sig c)))
curry' = lam0 $ \ f -> lam0 $ \ a -> lam0 $ \ b -> f $$ inlr a b

uncurry' :: Expr val comp => comp sig (comp sig (comp sig a -> comp sig (comp sig b -> comp sig c)) -> comp sig (comp sig (a, b) -> comp sig c))
uncurry' = lam0 $ \ f -> lam0 $ \ ab -> f $$ exl ab $$ exr ab

get :: (Expr val comp, Member (State (comp sig s)) sig) => comp sig s
get = send (Eff Get id)

put :: (Expr val comp, Member (State (comp sig s)) sig) => comp sig (comp sig s -> comp sig ())
put = lam0 $ \ s -> send (Eff (Put s) (const unit))

runState :: Expr val comp => comp sig (comp sig s -> comp sig (comp (State (comp sig s)) a -> comp sig (s, a)))
runState = lam0 $ \ s -> lam1 $ \case
  Left a                 -> inlr s a
  Right (Eff Get     k) -> runState $$ s $$ k s
  Right (Eff (Put s) k) -> runState $$ s $$ k ()

execState :: Expr val comp => comp sig (comp sig s -> comp sig (comp (State (comp sig s)) a -> comp sig a))
execState = lam0 $ \ s -> lam1 $ \case
  Left a                 -> a
  Right (Eff Get     k) -> execState $$ s $$ k s
  Right (Eff (Put s) k) -> execState $$ s $$ k ()


postIncr :: forall val comp sig . (Expr val comp, Num (comp sig Int), Member (State (comp sig Int)) sig) => comp sig Int
postIncr = get <& (put $$ (get + (1 :: comp sig Int)))


empty :: (Expr val comp, Member Empty sig) => comp sig a
empty = send (Eff Empty id)

runEmpty :: Expr val comp => comp sig (comp sig a -> comp sig (comp Empty a -> comp sig a))
runEmpty = lam0 $ \ a -> lam1 $ \case
  Left x              -> x
  Right (Eff Empty _) -> a

execEmpty :: Expr val comp => comp sig (comp Empty a -> comp sig Bool)
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
