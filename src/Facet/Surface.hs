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
import Facet.Name
import Facet.Span
import Facet.Stack
import Facet.Syntax

-- Expressions

data Expr f
  = Var (Maybe MName) DName
  | Hole UName
  | Type
  | TInterface
  | TString
  | TComp (f (Comp f))
  | Lam [Clause f]
  | Thunk (f (Expr f))
  | Force (f (Expr f))
  | App (f (Expr f)) (f (Expr f))
  | As (f (Expr f)) (f (Type f))
  | String Text

deriving instance (forall x . Eq   x => Eq   (f x)) => Eq   (Expr f)
deriving instance (forall x . Show x => Show (f x)) => Show (Expr f)

type Type = Expr


free :: DName -> Expr f
free = Var Nothing

qual :: QName -> Expr f
qual (m :.: n) = Var (Just m) n


data Comp f = Comp
  { bindings :: [f (Binding f)]
  , delta    :: [f (Interface f)]
  , type'    :: f (Type f)
  }

deriving instance (forall x . Eq   x => Eq   (f x)) => Eq   (Comp f)
deriving instance (forall x . Show x => Show (f x)) => Show (Comp f)

data Binding f = Binding
  { pl    :: Pl
  , names :: NonEmpty UName
  -- FIXME: wrap this in Maybe so we can distinguish values from parametric computations (as in the branches passed to if)
  , delta :: [f (Interface f)]
  , type' :: f (Type f)
  }

deriving instance (forall x . Eq   x => Eq   (f x)) => Eq   (Binding f)
deriving instance (forall x . Show x => Show (f x)) => Show (Binding f)


data Interface f = Interface (f (Maybe MName, DName)) (Stack (f (Type f)))

deriving instance (forall x . Eq   x => Eq   (f x)) => Eq   (Interface f)
deriving instance (forall x . Show x => Show (f x)) => Show (Interface f)


data Clause f = Clause (f (Pattern f)) (f (Expr f))

deriving instance (forall x . Eq   x => Eq   (f x)) => Eq   (Clause f)
deriving instance (forall x . Show x => Show (f x)) => Show (Clause f)


data Pattern f
  = PWildcard
  | PVar UName
  | PCon UName [f (Pattern f)]
  | PEff UName [f (Pattern f)] UName
  -- FIXME: catch-all effect patterns

deriving instance (forall x . Eq   x => Eq   (f x)) => Eq   (Pattern f)
deriving instance (forall x . Show x => Show (f x)) => Show (Pattern f)


-- Declarations

data Decl f = Decl (f (Comp f)) (Def f)

deriving instance (forall x . Eq   x => Eq   (f x)) => Eq   (Decl f)
deriving instance (forall x . Show x => Show (f x)) => Show (Decl f)


data Def f
  = DataDef [f (UName ::: f (Comp f))]
  | InterfaceDef [f (UName ::: f (Comp f))]
  | TermDef (f (Expr f))

deriving instance (forall x . Eq   x => Eq   (f x)) => Eq   (Def f)
deriving instance (forall x . Show x => Show (f x)) => Show (Def f)



-- Modules

data Module f = Module
  { name      :: MName
  , imports   :: [f Import]
  -- FIXME: store source references for operators’ definitions, for error reporting
  , operators :: [(Op, Assoc)]
  , defs      :: [f (DName, f (Decl f))]
  }

deriving instance (forall x . Eq   x => Eq   (f x)) => Eq   (Module f)
deriving instance (forall x . Show x => Show (f x)) => Show (Module f)


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


annUnary :: (Ann (Expr Ann) -> Expr Ann) -> Ann (Expr Ann) -> Ann (Expr Ann)
annUnary f a = Ann (ann a) Nil (f a)

annBinary :: (Ann (Expr Ann) -> Ann (Expr Ann) -> Expr Ann) -> Ann (Expr Ann) -> Ann (Expr Ann) -> Ann (Expr Ann)
annBinary f a b = Ann (ann a <> ann b) Nil (f a b)


newtype Comment = Comment { getComment :: Text }
  deriving (Eq, Show)
