{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Polarized
( Kind(..)
, Type(..)
, XType(..)
, Expr(..)
, Term(..)
, evalTerm
, Binding(..)
, fromV
, V(..)
, vvar
, velim
, K(..)
, Elab(..)
, Eval(..)
, Eval1(..)
, eval1
) where

import Control.Applicative (liftA2)
import Control.Carrier.Reader
import Data.Foldable (foldl')
import Data.Function (on)
import Facet.Name hiding (T)
import Facet.Quote
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
  deriving (Eq, Ord, Show) via Quoting XType Type

infixr 2 :->
infixr 7 :><
infixl 2 :>-

instance Quote Type XType where
  quote = \case
    TVar k d'  -> Quoter (\ d -> XTVar k (toIndexed d d'))
    Up t       -> XUp <$> quote t
    Bot        -> pure XBot
    a :-> b    -> liftA2 (:->:) (quote a) (quote b)
    ForAll k b -> XForAll k <$> quoteBinder (Quoter (TVar k)) b
    Down t     -> XDown <$> quote t
    One        -> pure XOne
    a :>< b    -> liftA2 (:><:) (quote a) (quote b)
    b :>- a    -> liftA2 (:>-:) (quote b) (quote a)


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
  | CTLam Kind Term
  | CLam Term
  | CMu Term Coterm
  deriving (Eq, Ord, Show)

data Coterm
  = CApp Term Coterm
  | CInst Type Coterm
  | CRet Index
  deriving (Eq, Ord, Show)

evalTerm :: Snoc Binding -> Snoc K -> Term -> V
evalTerm env kenv = \case
  CVar i    -> fromV (env ! getIndex i)
  CTLam k b -> TLam k (\ _T -> evalTerm (env :> T _T) kenv b)
  CLam b    -> Lam (\ a -> evalTerm (env :> V a) kenv b)
  CMu v k   -> foldl' velim (evalTerm env kenv v) (evalCoterm env (kenv :> Ret (Level (length kenv))) k)

evalCoterm :: Snoc Binding -> Snoc K -> Coterm -> [K]
evalCoterm env kenv = go
  where
  go = \case
    CApp a k  -> App (evalTerm env kenv a) : go k
    CInst t k -> Inst t : go k
    CRet i    -> [Ret (toLeveled (Level (length kenv)) i)]

data Binding
  = V V
  | T Type

fromV :: Binding -> V
fromV = \case
  V v -> v
  T _ -> error "fromV: type binding"


data V
  = Ne Level (Snoc K)
  -- negative
  | TLam Kind (Type -> V)
  | Lam (V -> V)

instance Eq V where
  (==) = (==) `on` quoteV 0 0

instance Ord V where
  compare = compare `on` quoteV 0 0

instance Show V where
  showsPrec p = showsPrec p . quoteV 0 0

quoteV :: Level -> Level -> V -> Term
quoteV lv lk = \case
  Ne l sp  -> CMu (CVar (toIndexed lv l)) (foldr (\case
    App v  -> CApp (quoteV lv lk v)
    Inst t -> CInst t
    Ret i  -> const (CRet (toIndexed lk i))) (CRet (Index 0)) sp)
  TLam k f -> CTLam k (quoteV (succ lv) lk (f (TVar k lv)))
  Lam f    -> CLam (quoteV (succ lv) lk (f (vvar lv)))


vvar :: Level -> V
vvar l = Ne l Nil

velim :: V -> K -> V
velim = curry $ \case
  (Ne v sp,  k)      -> Ne v (sp :> k)
  (Lam f,    App a)  -> f a
  (Lam{},    k)      -> error $ "cannot eliminate Lam with " <> show k
  (TLam _ f, Inst t) -> f t
  (TLam{},   k)      -> error $ "cannot eliminate TLam with " <> show k


data K
  = App V
  | Inst Type
  | Ret Level
  deriving (Eq, Ord, Show)


newtype Elab a = Elab { elab :: [(String, Type)] -> Maybe a }
  deriving (Functor)
  deriving (Applicative) via ReaderC [(String, Type)] Maybe


class Eval t e v | t -> e v where
  eval :: Snoc e -> t -> v

class Eval1 t v | t -> v where
  liftEvalWith :: (Snoc e -> s -> u) -> Snoc e -> t s -> v u

eval1 :: (Eval s e u, Eval1 t v) => Snoc e -> t s -> v u
eval1 = liftEvalWith eval
