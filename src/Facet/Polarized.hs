{-# LANGUAGE FunctionalDependencies #-}
module Facet.Polarized
( Kind(..)
, Type(..)
, XType(..)
, evalType
, Expr(..)
, Term(..)
, evalTerm
, Coterm(..)
, evalCoterm
, Val(..)
, vvar
, velim
, Coval(..)
, Elab(..)
, Quote(..)
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


evalType :: Snoc Type -> XType -> Type
evalType env = \case
  XTVar _ i   -> env ! getIndex i
  XUp t       -> Up (evalType env t)
  XBot        -> Bot
  a :->: b    -> evalType env a :-> evalType env b
  XForAll k b -> ForAll k (\ _A -> evalType (env :> _A) b)
  XDown t     -> Down (evalType env t)
  XOne        -> One
  a :><: b    -> evalType env a :>< evalType env b
  b :>-: a    -> evalType env b :>- evalType env a


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
  | CElim Term Coterm

evalTerm :: Snoc Val -> Term -> Val
evalTerm env = \case
  CVar i    -> env ! getIndex i
  CLam b    -> Lam (\ a -> evalTerm (env :> a) b)
  CUnit     -> Unit
  CPair a b -> Pair (evalTerm env a) (evalTerm env b)
  CThunk b  -> Thunk (evalTerm env b)
  CElim t e -> velim (evalTerm env t) (evalCoterm env e)

data Coterm
  = CApp Term
  | CFst
  | CSnd
  | CForce

evalCoterm :: Snoc Val -> Coterm -> Coval
evalCoterm env = \case
  CApp a -> App (evalTerm env a)
  CFst   -> Fst
  CSnd   -> Snd
  CForce -> Force

data Val
  = Ne Level (Snoc Coval)
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

velim :: Val -> Coval -> Val
velim = curry $ \case
  (Ne v sp,  c)     -> Ne v (sp :> c)
  (Lam f,    App a) -> f a
  (Pair a _, Fst)   -> a
  (Pair _ b, Snd)   -> b
  (Thunk v,  Force) -> v
  (_,        _)     -> error "cannot elim"


data Coval
  = App Val
  | Fst
  | Snd
  | Force

instance Quote Coval Coterm where
  quote d = \case
    App a -> CApp (quote d a)
    Fst   -> CFst
    Snd   -> CSnd
    Force -> CForce


newtype Elab a = Elab { elab :: [(String, Type)] -> Maybe a }
  deriving (Functor)
  deriving (Applicative) via ReaderC [(String, Type)] Maybe


class Quote v t | v -> t where
  quote :: Level -> v -> t
