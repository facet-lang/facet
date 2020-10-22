module Facet.Surface
( -- * Expressions
  Expr(..)
, ($$)
, unApp
, Comp(..)
, Pattern(..)
  -- * Types
, Type(..)
, (-->)
, ($$$)
, unForAll
, unTApp
  -- * Declarations
, Decl(..)
, DDecl(..)
, unDDForAll
, TDecl(..)
, unTDForAll
  -- * Modules
, Module(..)
, Import(..)
  -- * Annotations
, Ann(..)
) where

import Control.Effect.Empty
import Data.Function (on)
import Data.List.NonEmpty (NonEmpty)
import Facet.Name
import Facet.Span
import Facet.Stack
import Facet.Syntax hiding (out)

-- Expressions

data Expr
  = Qual QName
  | Free DName
  | Bound Index
  | Hole UName
  | Comp (Ann Comp)
  | Ann Expr :$ Ann Expr
  -- FIXME: tupling/unit should take a list of expressions
  deriving (Show)

infixl 9 :$


($$) :: Ann Expr -> Ann Expr -> Ann Expr
f $$ a = Ann (ann f <> ann a) (f :$ a)

infixl 9 $$


unApp :: Has Empty sig m => Expr -> m (Ann Expr, Ann Expr)
unApp = \case
  f :$ a -> pure (f, a)
  _      -> empty


data Comp
  = Expr (Ann Expr)
  | Clauses [(NonEmpty (Ann Pattern), Ann Expr)]
  deriving (Show)


data Pattern
  = PVar UName
  | PCon UName (Stack (Ann Pattern))
  | PEff UName (Stack (Ann Pattern)) UName
  deriving (Show)


-- Types

data Type
  = TQual QName
  | TFree DName
  | TBound Index
  | THole UName
  | Type
  | (UName ::: Ann Type) :=> Ann Type
  | Ann Type :$$ Ann Type
  | Ann Type :-> Ann Type
  deriving (Show)

infixr 1 :=>
infixl 9 :$$
infixr 1 :->


(-->) :: Ann Type -> Ann Type -> Ann Type
a --> b = Ann (ann a <> ann b) (a :-> b)

infixr 1 -->

($$$) :: Ann Type -> Ann Type -> Ann Type
f $$$ a = Ann (ann f <> ann a) (f :$$ a)

infixl 9 $$$

unForAll :: Has Empty sig m => Type -> m (UName ::: Ann Type, Ann Type)
unForAll = \case{ t :=> b -> pure (t, b) ; _ -> empty }

unTApp :: Has Empty sig m => Type -> m (Ann Type, Ann Type)
unTApp = \case{ f :$$ a -> pure (f, a) ; _ -> empty }


-- Declarations

data Decl
  = DDecl (Ann DDecl)
  | TDecl (Ann TDecl)
  deriving Show

data DDecl
  = DDForAll (Pl_ UName ::: Ann Type) (Ann DDecl)
  | DDBody (Ann Type) [Ann (UName ::: Ann Type)]
  deriving (Show)

unDDForAll :: Has Empty sig m => DDecl -> m (Pl_ UName ::: Ann Type, Ann DDecl)
unDDForAll = \case{ DDForAll t b -> pure (t, b) ; _ -> empty }


data TDecl
  = TDForAll (Pl_ UName ::: Ann Type) (Ann TDecl)
  | TDBody (Ann Type) (Ann Expr)
  deriving (Show)

unTDForAll :: Has Empty sig m => TDecl -> m (Pl_ UName ::: Ann Type, Ann TDecl)
unTDForAll = \case{ TDForAll t b -> pure (t, b) ; _ -> empty }


-- Modules

data Module = Module { name :: MName, imports :: [Ann Import], defs :: [Ann (DName, Ann Decl)] }
  deriving (Show)

newtype Import = Import { name :: MName }
  deriving (Show)


-- Annotations

data Ann a = Ann
  { ann :: Span
  , out :: a
  }
  deriving (Foldable, Functor, Traversable)

instance Eq a => Eq (Ann a) where
  (==) = (==) `on` out

instance Ord a => Ord (Ann a) where
  compare = compare `on` out

instance Show a => Show (Ann a) where
  showsPrec p = showsPrec p . out
