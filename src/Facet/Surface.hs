{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Surface
( -- * Expressions
  Expr(..)
, Type
, free
, qual
, Comp(..)
, Binding(..)
, Interface(..)
, Clause(..)
, Pattern(..)
  -- * Declarations
, Decl(..)
, Def(..)
  -- * Modules
, Module(..)
, Import(..)
  -- * Annotations
, Ann(..)
, annUnary
, annBinary
, Comment(..)
) where

import Data.Function (on)
import Data.List.NonEmpty (NonEmpty)
import Data.Text (Text)
import Data.Void
import Facet.Name
import Facet.Span
import Facet.Stack
import Facet.Syntax

-- Expressions

data Expr f a
  = Var (Maybe MName) DName
  | Hole UName
  | Type
  | TInterface
  | TString
  | TComp (f (Comp f a))
  | Lam [Clause f a]
  | Thunk (f (Expr f a))
  | Force (f (Expr f a))
  | App (f (Expr f a)) (f (Expr f a))
  | As (f (Expr f a)) (f (Type f a))
  | String Text
  | M a
  deriving (Foldable, Functor, Traversable)

deriving instance (Eq   a, forall x . Eq   x => Eq   (f x)) => Eq   (Expr f a)
deriving instance (Show a, forall x . Show x => Show (f x)) => Show (Expr f a)

type Type = Expr


free :: DName -> Expr f a
free = Var Nothing

qual :: QName -> Expr f a
qual (m :.: n) = Var (Just m) n


data Comp f a = Comp
  { bindings :: [f (Binding f a)]
  , delta    :: [f (Interface f a)]
  , type'    :: f (Type f a)
  }
  deriving (Foldable, Functor, Traversable)

deriving instance (Eq   a, forall x . Eq   x => Eq   (f x)) => Eq   (Comp f a)
deriving instance (Show a, forall x . Show x => Show (f x)) => Show (Comp f a)

data Binding f a = Binding
  { pl    :: Pl
  , names :: NonEmpty UName
  -- FIXME: wrap this in Maybe so we can distinguish values from parametric computations (as in the branches passed to if)
  , delta :: [f (Interface f a)]
  , type' :: f (Type f a)
  }
  deriving (Foldable, Functor, Traversable)

deriving instance (Eq   a, forall x . Eq   x => Eq   (f x)) => Eq   (Binding f a)
deriving instance (Show a, forall x . Show x => Show (f x)) => Show (Binding f a)


data Interface f a = Interface (f (Maybe MName, DName)) (Stack (f (Type f a)))
  deriving (Foldable, Functor, Traversable)

deriving instance (Eq   a, forall x . Eq   x => Eq   (f x)) => Eq   (Interface f a)
deriving instance (Show a, forall x . Show x => Show (f x)) => Show (Interface f a)


data Clause f a = Clause (f (Pattern f a)) (f (Expr f a))
  deriving (Foldable, Functor, Traversable)

deriving instance (Eq   a, forall x . Eq   x => Eq   (f x)) => Eq   (Clause f a)
deriving instance (Show a, forall x . Show x => Show (f x)) => Show (Clause f a)


data Pattern f a
  = PWildcard
  | PVar UName
  | PCon UName [f (Pattern f a)]
  | PEff UName [f (Pattern f a)] UName
  -- FIXME: catch-all effect patterns
  deriving (Foldable, Functor, Traversable)

deriving instance (Eq   a, forall x . Eq   x => Eq   (f x)) => Eq   (Pattern f a)
deriving instance (Show a, forall x . Show x => Show (f x)) => Show (Pattern f a)


-- Declarations

data Decl f a = Decl (f (Comp f a)) (Def f a)
  deriving (Foldable, Functor, Traversable)

deriving instance (Eq   a, forall x . Eq   x => Eq   (f x)) => Eq   (Decl f a)
deriving instance (Show a, forall x . Show x => Show (f x)) => Show (Decl f a)


data Def f a
  = DataDef [f (UName ::: f (Comp f a))]
  | InterfaceDef [f (UName ::: f (Comp f a))]
  | TermDef (f (Expr f a))
  deriving (Foldable, Functor, Traversable)

deriving instance (Eq   a, forall x . Eq   x => Eq   (f x)) => Eq   (Def f a)
deriving instance (Show a, forall x . Show x => Show (f x)) => Show (Def f a)



-- Modules

data Module f a = Module
  { name      :: MName
  , imports   :: [f Import]
  -- FIXME: store source references for operators’ definitions, for error reporting
  , operators :: [(Op, Assoc)]
  , defs      :: [f (DName, f (Decl f a))]
  }
  deriving (Foldable, Functor, Traversable)

deriving instance (Eq   a, forall x . Eq   x => Eq   (f x)) => Eq   (Module f a)
deriving instance (Show a, forall x . Show x => Show (f x)) => Show (Module f a)


newtype Import = Import { name :: MName }
  deriving (Eq, Show)


-- Annotations

data Ann a = Ann
  { ann      :: Span
  , comments :: Stack (Span, Comment)
  , out      :: a
  }
  deriving (Foldable, Functor, Traversable)

instance Eq a => Eq (Ann a) where
  (==) = (==) `on` out

instance Ord a => Ord (Ann a) where
  compare = compare `on` out

instance Show a => Show (Ann a) where
  showsPrec p = showsPrec p . out


annUnary :: (Ann (Expr Ann Void) -> Expr Ann Void) -> Ann (Expr Ann Void) -> Ann (Expr Ann Void)
annUnary f a = Ann (ann a) Nil (f a)

annBinary :: (Ann (Expr Ann Void) -> Ann (Expr Ann Void) -> Expr Ann Void) -> Ann (Expr Ann Void) -> Ann (Expr Ann Void) -> Ann (Expr Ann Void)
annBinary f a b = Ann (ann a <> ann b) Nil (f a b)


newtype Comment = Comment { getComment :: Text }
  deriving (Eq, Show)
