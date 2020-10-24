module Facet.Surface
( -- * Expressions
  Expr(..)
, Type
, Var(..)
, free
, qual
, bound
, Binding(..)
, Delta(..)
, ($$)
, Comp(..)
, Pattern(..)
  -- * Declarations
, Decl(..)
, DDecl(..)
, TDecl(..)
  -- * Modules
, Module(..)
, Import(..)
  -- * Annotations
, Ann(..)
) where

import Data.Function (on)
import Data.List.NonEmpty (NonEmpty)
import Facet.Name
import Facet.Span
import Facet.Stack
import Facet.Syntax hiding (out)

-- Expressions

data Expr
  = Var Var
  | Hole UName
  | Type
  | Interface
  | ForAll Binding (Ann Expr)
  | Comp (Ann Comp)
  | App (Ann Expr) (Ann Expr)
  -- FIXME: tupling/unit should take a list of expressions
  deriving (Eq, Show)

type Type = Expr


data Var
  = Free (Maybe MName) DName
  | Bound Index
  deriving (Eq, Show)

free :: DName -> Expr
free n = Var $ Free Nothing n

qual :: QName -> Expr
qual (m :.: n) = Var $ Free (Just m) n

bound :: Index -> Expr
bound = Var . Bound


data Binding = Binding
  { _pl   :: Pl
  , name  :: UName
  , delta :: [Ann Delta]
  , type' :: Ann Type
  }
  deriving (Eq, Show)

data Delta = Delta (Ann (Maybe MName, DName)) (Stack (Ann Type))
  deriving (Eq, Show)


($$) :: Ann Expr -> Ann Expr -> Ann Expr
f $$ a = Ann (ann f <> ann a) (App f a)

infixl 9 $$


data Comp
  = Expr (Ann Expr)
  | Clauses [(NonEmpty (Ann Pattern), Ann Expr)]
  deriving (Eq, Show)


data Pattern
  = PVar UName
  | PCon UName (Stack (Ann Pattern))
  | PEff UName (Stack (Ann Pattern)) UName
  deriving (Eq, Show)


-- Declarations

data Decl
  = DDecl (Ann DDecl)
  | TDecl (Ann TDecl)
  deriving (Eq, Show)

data DDecl
  = DDForAll Binding (Ann DDecl)
  | DDBody (Ann Type) [Ann (UName ::: Ann Type)]
  deriving (Eq, Show)

data TDecl
  = TDForAll Binding (Ann TDecl)
  | TDBody (Ann Type) (Ann Expr)
  deriving (Eq, Show)


-- Modules

-- FIXME: model operators and their associativities for parsing.
data Module = Module { name :: MName, imports :: [Ann Import], defs :: [Ann (DName, Ann Decl)] }
  deriving (Eq, Show)

newtype Import = Import { name :: MName }
  deriving (Eq, Show)


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
