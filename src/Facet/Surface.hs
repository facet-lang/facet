module Facet.Surface
( -- * Expressions
  Expr(..)
, Var(..)
, free
, qual
, bound
, (-->)
, Binding(..)
, Delta(..)
, unForAll
, ($$)
, unApp
, Comp(..)
, Pattern(..)
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
  = Var Var
  | Hole UName
  | Type
  | Interface
  | ForAll Binding (Ann Expr)
  | Comp (Ann Comp)
  | App (Ann Expr) (Ann Expr)
  -- FIXME: tupling/unit should take a list of expressions
  deriving (Eq, Show)


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

(-->) :: Ann Expr -> Ann Expr -> Ann Expr
a --> b = Ann (ann a <> ann b) (ForAll (Binding Nothing [] a) b)

infixr 1 -->

data Binding = Binding
  { name  :: Maybe UName
  , delta :: [Ann Delta]
  , type' :: Ann Expr
  }
  deriving (Eq, Show)

data Delta = Delta (Ann (Maybe MName, DName)) (Stack (Ann Var))
  deriving (Eq, Show)

unForAll :: Has Empty sig m => Expr -> m (Binding, Ann Expr)
unForAll = \case{ ForAll t b -> pure (t, b) ; _ -> empty }


($$) :: Ann Expr -> Ann Expr -> Ann Expr
f $$ a = Ann (ann f <> ann a) (App f a)

infixl 9 $$

unApp :: Has Empty sig m => Expr -> m (Ann Expr, Ann Expr)
unApp = \case
  App f a -> pure (f, a)
  _       -> empty


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
  = DDForAll (Pl_ UName ::: Ann Expr) (Ann DDecl)
  | DDBody (Ann Expr) [Ann (UName ::: Ann Expr)]
  deriving (Eq, Show)

unDDForAll :: Has Empty sig m => DDecl -> m (Pl_ UName ::: Ann Expr, Ann DDecl)
unDDForAll = \case{ DDForAll t b -> pure (t, b) ; _ -> empty }


data TDecl
  = TDForAll (Pl_ UName ::: Ann Expr) (Ann TDecl)
  | TDBody (Ann Expr) (Ann Expr)
  deriving (Eq, Show)

unTDForAll :: Has Empty sig m => TDecl -> m (Pl_ UName ::: Ann Expr, Ann TDecl)
unTDForAll = \case{ TDForAll t b -> pure (t, b) ; _ -> empty }


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
