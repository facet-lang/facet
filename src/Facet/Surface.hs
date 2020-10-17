{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Surface
( -- * Expressions
  Expr(..)
, unApp
, Comp(..)
, Pattern(..)
  -- * Types
, Type(..)
, unForAll
, unTApp
, aeq
  -- * Declarations
, Decl(..)
, unDForAll
, unDArrow
, DeclBody(..)
  -- * Modules
, Module(..)
) where

import Control.Applicative (liftA2)
import Control.Effect.Empty
import Data.Function (on)
import Data.List.NonEmpty (NonEmpty)
import Data.Monoid (First(..))
import Data.Text (Text)
import Facet.Name
import Facet.Syntax
import Text.Parser.Position

-- Expressions

data Expr a
  = Free DName
  | Bound Index
  | Hole Text
  | Comp (Spanned (Comp a))
  | Spanned (Expr a) :$ Spanned (Expr a)
  | Unit
  | Spanned (Expr a) :* Spanned (Expr a)
  -- FIXME: tupling/unit should take a list of expressions
  deriving (Foldable, Functor, Show, Traversable)

infixl 9 :$
infixl 7 :*


unApp :: Has Empty sig m => Expr a -> m (Spanned (Expr a), Spanned (Expr a))
unApp = \case
  f :$ a -> pure (f, a)
  _      -> empty


data Comp a
  = Expr (Spanned (Expr a))
  | Clauses [(NonEmpty (Spanned (Pattern UName)), Spanned (Expr a))]
  deriving (Foldable, Functor, Show, Traversable)


data Pattern a
  = Wildcard
  | Var a
  | Con CName [Spanned (Pattern a)]
  | Tuple [Spanned (Pattern a)]
  deriving (Foldable, Functor, Show, Traversable)


-- Types

data Type a
  = TFree DName
  | TBound Index
  | THole Text
  | Type
  | Void
  | TUnit
  | (UName ::: Spanned (Type a)) :=> Spanned (Type a)
  | Spanned (Type a) :$$ Spanned (Type a)
  | Spanned (Type a) :-> Spanned (Type a)
  | Spanned (Type a) :** Spanned (Type a)
  deriving (Foldable, Functor, Show, Traversable)

infixr 1 :=>
infixl 9 :$$
infixr 2 :->
infixl 7 :**


unForAll :: Has Empty sig m => Type a -> m (UName ::: Spanned (Type a), Spanned (Type a))
unForAll = \case{ t :=> b -> pure (t, b) ; _ -> empty }

unTApp :: Has Empty sig m => Type a -> m (Spanned (Type a), Spanned (Type a))
unTApp = \case{ f :$$ a -> pure (f, a) ; _ -> empty }


aeq :: Type a -> Type a -> Bool
aeq t1 t2 = case (t1, t2) of
  (TFree  n1,          TFree  n2)          -> n1 == n2
  (TBound n1,          TBound n2)          -> n1 == n2
  (Type,               Type)               -> True
  (TUnit,              TUnit)              -> True
  ((n1 ::: t1) :=> b1, (n2 ::: t2) :=> b2) -> n1 == n2 && aeq' t1 t2 && aeq' b1 b2
  (f1 :$$ a1,          f2 :$$ a2)          -> aeq' f1 f2 && aeq' a1 a2
  (a1 :-> b1,          a2 :-> b2)          -> aeq' a1 a2 && aeq' b1 b2
  (l1 :** r1,          l2 :** r2)          -> aeq' l1 l2 && aeq' r1 r2
  _                                        -> False
  where
  aeq' = fmap and . (liftA2 aeq `on` extract)
  extract = getFirst . foldMap (First . Just)


-- Declarations

data Decl a
  = (UName ::: Spanned (Type a)) :==> Spanned (Decl a)
  | (UName ::: Spanned (Type a)) :--> Spanned (Decl a)
  | Spanned (Type a) := DeclBody a
  deriving (Foldable, Functor, Show, Traversable)

infix 1 :=
infixr 1 :==>
infixr 1 :-->


unDForAll :: Has Empty sig m => Decl a -> m (UName ::: Spanned (Type a), Spanned (Decl a))
unDForAll = \case{ t :==> b -> pure (t, b) ; _ -> empty }

unDArrow :: Has Empty sig m => Decl a -> m (UName ::: Spanned (Type a), Spanned (Decl a))
unDArrow = \case{ t :--> b -> pure (t, b) ; _ -> empty }


data DeclBody a
  = DExpr (Spanned (Expr a))
  | DType (Spanned (Type a))
  | DData [Spanned (CName ::: Spanned (Type a))]
  deriving (Foldable, Functor, Show, Traversable)


-- Modules

-- FIXME: imports
data Module a = Module { name :: MName, defs :: [Spanned (DName, Spanned (Decl a))] }
  deriving (Foldable, Functor, Show, Traversable)
