module Facet.Polarized
( Kind(..)
, Type(..)
, XType(..)
, evalType
, quoteType
, Expr(..)
, Term(..)
, evalTerm
, Coterm(..)
, evalCoterm
, Val(..)
, vvar
, Coval(..)
, Elab(..)
) where

import Control.Carrier.Reader
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

quoteType :: Level -> Type -> XType
quoteType d = \case
  TVar k d'  -> XTVar k (levelToIndex d d')
  Up t       -> XUp (quoteType d t)
  Bot        -> XBot
  a :-> b    -> quoteType d a :->: quoteType d b
  ForAll k b -> XForAll k (quoteType (succ d) (b (TVar k d)))
  Down t     -> XDown (quoteType d t)
  One        -> XOne
  a :>< b    -> quoteType d a :><: quoteType d b
  b :>- a    -> quoteType d b :>-: quoteType d a


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

evalTerm :: Snoc Val -> Term -> Val
evalTerm env = \case
  CVar i    -> env ! getIndex i
  CLam b    -> Lam (\ a -> evalTerm (env :> a) b)
  CUnit     -> Unit
  CPair a b -> Pair (evalTerm env a) (evalTerm env b)
  CThunk b  -> Thunk (evalTerm env b)

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

vvar :: Level -> Val
vvar l = Ne l Nil

data Coval
  = App Val
  | Fst
  | Snd
  | Force

newtype Elab a = Elab { elab :: [(String, Type)] -> Maybe a }
  deriving (Functor)
  deriving (Applicative) via ReaderC [(String, Type)] Maybe
