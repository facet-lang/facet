{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Polarized
( Kind(..)
, Type(..)
, XType(..)
, Expr(..)
, Term(..)
, Val(..)
, vvar
, velim
, Co(..)
, Elab(..)
, Quote(..)
, Eval(..)
) where

import Control.Carrier.Reader
import Data.Foldable (foldl')
import Facet.Name
import Facet.Snoc

data Kind
  = Type
  | Kind :=> Kind
  deriving (Eq, Ord, Show)

infixr 2 :=>

data Type
  = TVar Kind Level
  -- negative
  | Up Type
  | Bot
  | Type :-> Type
  | ForAll Kind (Type -> Type)
  -- positive
  | Down Type
  | One
  | Type :>< Type
  | Type :>- Type

infixr 2 :->
infixr 7 :><
infixl 2 :>-

instance Quote Type XType where
  quote d = \case
    TVar k d'  -> XTVar k (levelToIndex d d')
    Up t       -> XUp (quote d t)
    Bot        -> XBot
    a :-> b    -> quote d a :->: quote d b
    ForAll k b -> XForAll k (quote (succ d) (b (TVar k d)))
    Down t     -> XDown (quote d t)
    One        -> XOne
    a :>< b    -> quote d a :><: quote d b
    b :>- a    -> quote d b :>-: quote d a


data XType
  = XTVar Kind Index
  -- negative
  | XUp XType
  | XBot
  | XType :->: XType
  | XForAll Kind XType
  -- positive
  | XDown XType
  | XOne
  | XType :><: XType
  | XType :>-: XType
  deriving (Eq, Ord, Show)

infixr 2 :->:
infixr 7 :><:
infixl 2 :>-:

instance Eval XType Type Type where
  eval env = \case
    XTVar _ i   -> env ! getIndex i
    XUp t       -> Up (eval env t)
    XBot        -> Bot
    a :->: b    -> eval env a :-> eval env b
    XForAll k b -> ForAll k (\ _A -> eval (env :> _A) b)
    XDown t     -> Down (eval env t)
    XOne        -> One
    a :><: b    -> eval env a :>< eval env b
    b :>-: a    -> eval env b :>- eval env a


data Expr
  = XVar String
  | XLam String Expr
  | XApp Expr Expr

data Term
  = CVar Index
  | CLam Term
  | CUnit
  | CPair Term Term
  | CThunk Term
  | CElim Term (Co Term)

instance Eval Term Val Val where
  eval env = \case
    CVar i    -> env ! getIndex i
    CLam b    -> Lam (\ a -> eval (env :> a) b)
    CUnit     -> Unit
    CPair a b -> Pair (eval env a) (eval env b)
    CThunk b  -> Thunk (eval env b)
    CElim t e -> velim (eval env t) (eval env e)

instance Eval (Co Term) Val (Co Val) where
  eval env = \case
    App a -> App (eval env a)
    Fst   -> Fst
    Snd   -> Snd
    Force -> Force

data Val
  = Ne Level (Snoc (Co Val))
  -- negative
  | Lam (Val -> Val)
  -- positive
  | Unit
  | Pair Val Val
  | Thunk Val

instance Quote Val Term where
  quote d = \case
    Ne l sp  -> foldl' (\ t c -> CElim t (quote d c)) (CVar (levelToIndex d l)) sp
    Lam f    -> CLam (quote (succ d) (f (vvar d)))
    Unit     -> CUnit
    Pair a b -> CPair (quote d a) (quote d b)
    Thunk b  -> CThunk (quote d b)


vvar :: Level -> Val
vvar l = Ne l Nil

velim :: Val -> Co Val -> Val
velim = curry $ \case
  (Ne v sp,  c)     -> Ne v (sp :> c)
  (Lam f,    App a) -> f a
  (Pair a _, Fst)   -> a
  (Pair _ b, Snd)   -> b
  (Thunk v,  Force) -> v
  (_,        _)     -> error "cannot elim"


data Co t
  = App t
  | Fst
  | Snd
  | Force
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Quote v t => Quote (Co v) (Co t) where
  quote d = \case
    App a -> App (quote d a)
    Fst   -> Fst
    Snd   -> Snd
    Force -> Force


newtype Elab a = Elab { elab :: [(String, Type)] -> Maybe a }
  deriving (Functor)
  deriving (Applicative) via ReaderC [(String, Type)] Maybe


class Quote v t | v -> t where
  quote :: Level -> v -> t

class Eval t e v | t -> e v where
  eval :: Snoc e -> t -> v
