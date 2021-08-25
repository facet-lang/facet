{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Polarized
( Kind(..)
, Type(..)
, XType(..)
, Expr(..)
, Term(..)
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
import Data.Foldable (foldl')
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
  | CElim Term (K Term)
  deriving (Eq, Ord, Show)

data Binding
  = V V
  | T Type

fromV :: Binding -> V
fromV = \case
  V v -> v
  T _ -> error "fromV: type binding"

instance Eval Term Binding V where
  eval env = \case
    CVar i    -> fromV (env ! getIndex i)
    CTLam k b -> TLam k (\ _T -> eval (env :> T _T) b)
    CLam b    -> Lam (\ a -> eval (env :> V a) b)
    CElim t e -> eval env t `velim` eval env e

instance Eval m e v => Eval (K m) e (K v) where
  eval = eval1

data V
  = Ne Level (Snoc (K V))
  -- negative
  | TLam Kind (Type -> V)
  | Lam (V -> V)
  deriving (Eq, Ord, Show) via Quoting Term V

instance Quote V Term where
  quote d = \case
    Ne l sp  -> foldl' (\ t c -> CElim t (quote d c)) (CVar (levelToIndex d l)) sp
    TLam k f -> CTLam k (quoteBinder (TVar k) d f)
    Lam f    -> CLam (quoteBinder vvar d f)


vvar :: Level -> V
vvar l = Ne l Nil

velim :: V -> K V -> V
velim = curry $ \case
  (Ne v sp,  k)      -> Ne v (sp :> k)
  (Lam f,    App a)  -> f a
  (Lam{},    k)      -> error $ "cannot eliminate Lam with " <> show k
  (TLam _ f, Inst t) -> f t
  (TLam{},   k)      -> error $ "cannot eliminate TLam with " <> show k


data K v
  = App v
  | Inst Type
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Quote1 K K where
  liftQuoteWith = fmap fmap

instance Quote v m => Quote (K v) (K m) where
  quote = quote1

instance Eval1 K K where
  liftEvalWith = fmap fmap


data C v
  = v :|: K v
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Quote1 C C where
  liftQuoteWith = fmap fmap

instance Quote v t => Quote (C v) (C t) where
  quote = quote1

instance Eval1 C C where
  liftEvalWith = fmap fmap

instance Eval m e v => Eval (C m) e (C v) where
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
