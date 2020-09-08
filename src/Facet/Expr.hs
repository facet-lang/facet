{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Expr
( Expr(..)
, Inst(..)
, var
, (<&)
, (&>)
, Unit(..)
, Pair(..)
, first
, second
, Eff(..)
  -- * Effects
, Sum(..)
, State(..)
, None
, Return(..)
  -- * Examples
, id'
, const'
, flip'
, get
, put
, runState
, execState
  -- * Signatures
, Has
) where

import Data.Kind (Type)

class Expr (repr :: (Type -> Type) -> (Type -> Type)) where
  lam :: (Inst eff (repr sig a) -> repr sig b) -> repr sig (a -> b)
  ($$) :: repr sig (a -> b) -> repr sig a -> repr sig b
  infixl 9 $$


data Inst eff a where
  Val :: a -> Inst eff a
  Eff :: eff a -> Inst eff a

var :: Inst None a -> a
var (Val a) = a
var (Eff e) = case e of {}


(<&) :: Expr repr => repr sig a -> repr sig b -> repr sig a
a <& b = const' $$ a $$ b

(&>) :: Expr repr => repr sig a -> repr sig b -> repr sig b
a &> b = flip' $$ const' $$ a $$ b

infixl 1 <&, &>


class Unit (repr :: (Type -> Type) -> (Type -> Type)) where
  unit :: repr sig ()


class Pair (repr :: (Type -> Type) -> (Type -> Type)) where
  inlr :: repr sig a -> repr sig b -> repr sig (a, b)
  exl :: repr sig (a, b) -> repr sig a
  exr :: repr sig (a, b) -> repr sig b

first :: (Expr repr, Pair repr) => repr sig (a -> a') -> repr sig (a, b) -> repr sig (a', b)
first f ab = inlr (f $$ exl ab) (exr ab)

second :: (Expr repr, Pair repr) => repr sig (b -> b') -> repr sig (a, b) -> repr sig (a, b')
second f ab = inlr (exl ab) (f $$ exr ab)


class Eff repr where
  inst :: sig (repr sig a) -> repr sig a


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

-- | The identity effect.
newtype Return a = Return a


-- Examples

id' :: Expr repr => repr sig (a -> a)
id' = lam var

const' :: Expr repr => repr sig (a -> b -> a)
const' = lam (lam . const . var)

flip' :: Expr repr => repr sig ((a -> b -> c) -> (b -> a -> c))
flip' = lam (\ f -> lam (\ b -> lam (\ a -> var f $$ var a $$ var b)))

get :: (Eff repr, Has (State (repr sig s)) sig) => repr sig s
get = inst (inj (Get id))

put :: (Eff repr, Expr repr, Unit repr, Has (State (repr sig s)) sig) => repr sig (s -> ())
put = lam $ \ s -> inst (inj (Put (var s) unit))

runState :: (Expr repr, Pair repr) => repr sig (s -> a -> (s, a))
runState = lam $ \ s -> lam $ \case
  Val a         -> inlr (var s) a
  Eff (Get   k) -> runState $$ var s $$ k (var s)
  Eff (Put s k) -> runState $$ s $$ k

execState :: Expr repr => repr sig (s -> a -> a)
execState = lam $ \ s -> lam $ \case
  Val a         -> a
  Eff (Get   k) -> execState $$ var s $$ k (var s)
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
