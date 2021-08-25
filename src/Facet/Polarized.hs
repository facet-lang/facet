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
, C(..)
, Elab(..)
, Eval(..)
, Eval1(..)
, eval1
) where

import Control.Carrier.Reader
import Data.Bifunctor
import Data.Foldable (foldl')
import Data.Function (on)
import Facet.Name
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
  quote d = \case
    TVar k d'  -> XTVar k (levelToIndex d d')
    Up t       -> XUp (quote d t)
    Bot        -> XBot
    a :-> b    -> quote d a :->: quote d b
    ForAll k b -> XForAll k (quoteBinder (TVar k) d b)
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
  | CTLam Kind Term
  | CLam Term
  | CMu (C Index Term)
  | CElim Term (K Index Term)
  deriving (Eq, Ord, Show)

evalTerm :: Snoc Binding -> Snoc (K Level V) -> Term -> V
evalTerm env kenv = \case
  CVar i        -> fromV (env ! getIndex i)
  CTLam k b     -> TLam k (\ _T -> evalTerm (env :> T _T) kenv b)
  CLam b        -> Lam (\ a -> evalTerm (env :> V a) kenv b)
  CMu (v :|: k) -> evalTerm env kenv v `velim` bimap (indexToLevel (Level (length kenv))) (evalTerm env kenv) k
  CElim t e     -> evalTerm env kenv t `velim` bimap (indexToLevel (Level (length kenv))) (evalTerm env kenv) e

data Binding
  = V V
  | T Type

fromV :: Binding -> V
fromV = \case
  V v -> v
  T _ -> error "fromV: type binding"


data V
  = Ne Level (Snoc (K Level V))
  -- negative
  | TLam Kind (Type -> V)
  | Lam (V -> V)
  | Mu (K Level V -> C Level V)

instance Eq V where
  (==) = (==) `on` quoteV 0 0

instance Ord V where
  compare = compare `on` quoteV 0 0

instance Show V where
  showsPrec p = showsPrec p . quoteV 0 0

quoteV :: Level -> Level -> V -> Term
quoteV lv lk = \case
  Ne l sp  -> foldl' (\ t c -> CElim t (bimap (levelToIndex lk) (quoteV lk lv) c)) (CVar (levelToIndex lv l)) sp
  TLam k f -> CTLam k (quoteBinderWith (`quoteV` lk) (TVar k) lv f)
  Lam f    -> CLam (quoteBinderWith (`quoteV` lk) vvar lv f)
  Mu f     -> CMu (bimap (levelToIndex lk) (quoteV lv (succ lk)) (f (Ret lk)))


vvar :: Level -> V
vvar l = Ne l Nil

velim :: V -> K Level V -> V
velim = curry $ \case
  (Ne v sp,  k)      -> Ne v (sp :> k)
  (Lam f,    App a)  -> f a
  (Lam{},    k)      -> error $ "cannot eliminate Lam with " <> show k
  (TLam _ f, Inst t) -> f t
  (TLam{},   k)      -> error $ "cannot eliminate TLam with " <> show k
  (Mu{},     k)      -> error $ "cannot eliminate Mu with " <> show k


data K i v
  = App v
  | Inst Type
  | Ret i
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bifunctor K where
  bimap f g = \case
    App c   -> App (g c)
    Inst ty -> Inst ty
    Ret i   -> Ret (f i)

instance Quote1 (K Level) (K Level) where
  liftQuoteWith = fmap fmap

instance Quote v m => Quote (K Level v) (K Level m) where
  quote = quote1

instance Eval1 (K Index) (K Index) where
  liftEvalWith = fmap fmap

instance Eval m e v => Eval (K Index m) e (K Index v) where
  eval = eval1


data C i v
  = v :|: K i v
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bifunctor C where
  bimap f g (v :|: k) = g v :|: bimap f g k

instance Quote1 (C Level) (C Level) where
  liftQuoteWith = fmap fmap

instance Quote v t => Quote (C Level v) (C Level t) where
  quote = quote1

instance Eval1 (C Index) (C Index) where
  liftEvalWith = fmap fmap

instance Eval m e v => Eval (C Index m) e (C Index v) where
  eval = eval1


newtype Elab a = Elab { elab :: [(String, Type)] -> Maybe a }
  deriving (Functor)
  deriving (Applicative) via ReaderC [(String, Type)] Maybe


class Eval t e v | t -> e v where
  eval :: Snoc e -> t -> v

class Eval1 t v | t -> v where
  liftEvalWith :: (Snoc e -> s -> u) -> Snoc e -> t s -> v u

eval1 :: (Eval s e u, Eval1 t v) => Snoc e -> t s -> v u
eval1 = liftEvalWith eval
