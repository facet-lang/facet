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
, send
  -- * Effects
, Sum(..)
, State(..)
, None
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
, Has
) where

import Data.Kind (Type)

class Expr (repr :: ((Type -> Type) -> (Type -> Type) -> (Type -> Type)) -> (Type -> Type)) where
  lam :: (Inst eff (repr sig) (repr sig') a -> repr sig b) -> repr sig (repr sig' a -> repr sig b)
  ($$) :: repr sig (repr sig' a -> repr sig b) -> repr sig' a -> repr sig b
  infixl 9 $$


data Inst eff (repr :: Type -> Type) (repr' :: Type -> Type) a where
  Val :: repr a -> Inst eff repr repr' a
  Eff :: eff repr repr' a -> Inst eff repr repr' a

var :: Inst None repr repr' a -> repr a
var (Val a) = a
var (Eff e) = case e of {}


(<&) :: Expr repr => repr sig a -> repr sig b -> repr sig a
a <& b = const' $$ a $$ b

(&>) :: Expr repr => repr sig a -> repr sig b -> repr sig b
a &> b = flip' $$ const' $$ a $$ b

infixl 1 <&, &>


class Unit (repr :: ((Type -> Type) -> (Type -> Type) -> (Type -> Type)) -> (Type -> Type)) where
  unit :: repr sig ()


class Pair (repr :: ((Type -> Type) -> (Type -> Type) -> (Type -> Type)) -> (Type -> Type)) where
  inlr :: repr sig a -> repr sig b -> repr sig (a, b)
  exl :: repr sig (a, b) -> repr sig a
  exr :: repr sig (a, b) -> repr sig b

first :: (Expr repr, Pair repr) => repr sig (repr sig a -> repr sig a') -> repr sig (a, b) -> repr sig (a', b)
first f ab = inlr (f $$ exl ab) (exr ab)

second :: (Expr repr, Pair repr) => repr sig (repr sig b -> repr sig b') -> repr sig (a, b) -> repr sig (a, b')
second f ab = inlr (exl ab) (f $$ exr ab)


class Eff repr where
  alg :: sig (repr sig) (repr sig) a -> repr sig a

send :: (Has eff sig, Eff repr) => eff (repr sig) (repr sig) a -> repr sig a
send = alg . inj


-- Effects

-- | Sum of effects represented as a binary tree.
data Sum l r (repr :: Type -> Type) (repr' :: Type -> Type) k
  = L (l repr repr' k)
  | R (r repr repr' k)

data State s (repr :: Type -> Type) (repr' :: Type -> Type) k
  = Get (repr s -> repr' k)
  | Put (repr s) (repr' k)

-- | No effects.
data None (repr :: Type -> Type) (repr' :: Type -> Type) k

-- | The identity effect.
newtype Return (repr :: Type -> Type) (repr' :: Type -> Type) a = Return (repr a)


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

get :: (Eff repr, Has (State s) sig) => repr sig s
get = send (Get id)

put :: (Eff repr, Expr repr, Unit repr, Has (State s) sig) => repr sig (repr sig s -> repr sig ())
put = lam $ \ s -> send (Put (var s) unit)

runState :: (Expr repr, Pair repr) => repr sig (repr sig s -> repr sig (repr (State s) a -> repr sig (s, a)))
runState = lam $ \ s -> lam $ \case
  Val a         -> inlr (var s) a
  Eff (Get   k) -> runState $$ var s $$ k (var s)
  Eff (Put s k) -> runState $$ s $$ k

execState :: Expr repr => repr sig (repr sig s -> repr sig (repr (State s) a -> repr sig a))
execState = lam $ \ s -> lam $ \case
  Val a         -> a
  Eff (Get   k) -> execState $$ var s $$ k (var s)
  Eff (Put s k) -> execState $$ s $$ k

execState' :: Expr repr => repr sig s -> repr (State s) a -> repr sig a
execState' s a = lam (\case
  Val a         -> a
  Eff (Get   k) -> execState' s (k s)
  Eff (Put s k) -> execState' s k) $$ a


-- Signatures

class Has (eff :: (Type -> Type) -> (Type -> Type) -> (Type -> Type)) (sig :: (Type -> Type) -> (Type -> Type) -> (Type -> Type)) where
  inj :: eff repr repr' a -> sig repr repr' a

instance Has eff eff where
  inj = id

instance Has eff (Sum eff sig) where
  inj = L

instance Has eff sig => Has eff (Sum non sig) where
  inj = R . inj
