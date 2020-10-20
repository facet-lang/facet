{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DuplicateRecordFields #-}
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
, DDecl(..)
, unDDForAll
, TDecl(..)
, unTDForAll
  -- * Modules
, Module(..)
, Import(..)
) where

import Control.Applicative (liftA2)
import Control.Effect.Empty
import Data.Function (on)
import Data.List.NonEmpty (NonEmpty)
import Data.Monoid (First(..))
import Facet.Name
import Facet.Syntax
import Text.Parser.Position

-- Expressions

data Expr
  = Free DName
  | Bound Index
  | Hole UName
  | Comp (Spanned Comp)
  | Spanned Expr :$ Spanned Expr
  -- FIXME: tupling/unit should take a list of expressions
  deriving (Show)

infixl 9 :$


unApp :: Has Empty sig m => Expr -> m (Spanned Expr, Spanned Expr)
unApp = \case
  f :$ a -> pure (f, a)
  _      -> empty


data Comp
  = Expr (Spanned Expr)
  | Clauses [(NonEmpty (Spanned Pattern), Spanned Expr)]
  deriving (Show)


data Pattern
  = PVar UName
  | PCon CName [Spanned Pattern]
  deriving (Show)


-- Types

data Type
  = TFree DName
  | TBound Index
  | THole UName
  | Type
  | (UName ::: Spanned Type) :=> Spanned Type
  | Spanned Type :$$ Spanned Type
  | Spanned Type :-> Spanned Type
  deriving (Show)

infixr 1 :=>
infixl 9 :$$
infixr 2 :->


unForAll :: Has Empty sig m => Type -> m (UName ::: Spanned Type, Spanned Type)
unForAll = \case{ t :=> b -> pure (t, b) ; _ -> empty }

unTApp :: Has Empty sig m => Type -> m (Spanned Type, Spanned Type)
unTApp = \case{ f :$$ a -> pure (f, a) ; _ -> empty }


aeq :: Type -> Type -> Bool
aeq t1 t2 = case (t1, t2) of
  (TFree  n1,          TFree  n2)          -> n1 == n2
  (TBound n1,          TBound n2)          -> n1 == n2
  (Type,               Type)               -> True
  ((n1 ::: t1) :=> b1, (n2 ::: t2) :=> b2) -> n1 == n2 && aeq' t1 t2 && aeq' b1 b2
  (f1 :$$ a1,          f2 :$$ a2)          -> aeq' f1 f2 && aeq' a1 a2
  (a1 :-> b1,          a2 :-> b2)          -> aeq' a1 a2 && aeq' b1 b2
  _                                        -> False
  where
  aeq' = fmap and . (liftA2 aeq `on` extract)
  extract = getFirst . foldMap (First . Just)


-- Declarations

data Decl
  = DDecl (Spanned DDecl)
  | TDecl (Spanned TDecl)
  deriving Show

data DDecl
  = DDForAll (Pl_ UName ::: Spanned Type) (Spanned DDecl)
  | DDBody (Spanned Type) [Spanned (CName ::: Spanned Type)]
  deriving (Show)

unDDForAll :: Has Empty sig m => DDecl -> m (Pl_ UName ::: Spanned Type, Spanned DDecl)
unDDForAll = \case{ DDForAll t b -> pure (t, b) ; _ -> empty }


data TDecl
  = TDForAll (Pl_ UName ::: Spanned Type) (Spanned TDecl)
  | TDBody (Spanned Type) (Spanned Expr)
  deriving (Show)

unTDForAll :: Has Empty sig m => TDecl -> m (Pl_ UName ::: Spanned Type, Spanned TDecl)
unTDForAll = \case{ TDForAll t b -> pure (t, b) ; _ -> empty }


-- Modules

data Module = Module { name :: MName, imports :: [Spanned Import], defs :: [Spanned (DName, Spanned Decl)] }
  deriving (Show)

newtype Import = Import { name :: MName }
  deriving (Show)
