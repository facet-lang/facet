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

data Expr
  = Var (Maybe MName) DName
  | Hole UName
  | Type
  | TInterface
  | TString
  | TComp (Ann Comp)
  | Lam [Clause]
  | Thunk (Ann Expr)
  | Force (Ann Expr)
  | App (Ann Expr) (Ann Expr)
  | As (Ann Expr) (Ann Type)
  | String Text
  deriving (Eq, Show)

type Type = Expr


free :: DName -> Expr
free = Var Nothing

qual :: QName -> Expr
qual (m :.: n) = Var (Just m) n


data Comp = Comp
  { bindings :: [Ann Binding]
  , delta    :: [Ann Interface]
  , type'    :: Ann Type
  }
  deriving (Eq, Show)

data Binding = Binding
  { pl    :: Pl
  , names :: NonEmpty UName
  -- FIXME: wrap this in Maybe so we can distinguish values from parametric computations (as in the branches passed to if)
  , delta :: [Ann Interface]
  , type' :: Ann Type
  }
  deriving (Eq, Show)

data Interface = Interface (Ann (Maybe MName, DName)) (Stack (Ann Type))
  deriving (Eq, Show)

data Clause = Clause (Ann Pattern) (Ann Expr)
  deriving (Eq, Show)


data Pattern
  = PWildcard
  | PVar UName
  | PCon UName [Ann Pattern]
  | PEff UName [Ann Pattern] UName
  -- FIXME: catch-all effect patterns
  deriving (Eq, Show)


-- Declarations

data Decl = Decl (Ann Comp) Def
  deriving (Eq, Show)

data Def
  = DataDef [Ann (UName ::: Ann Comp)]
  | InterfaceDef [Ann (UName ::: Ann Comp)]
  | TermDef (Ann Expr)
  deriving (Eq, Show)


-- Modules

data Module = Module
  { name      :: MName
  , imports   :: [Ann Import]
  -- FIXME: store source references for operators’ definitions, for error reporting
  , operators :: [(Op, Assoc)]
  , defs      :: [Ann (DName, Ann Decl)]
  }
  deriving (Eq, Show)

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


annUnary :: (Ann Expr -> Expr) -> Ann Expr -> Ann Expr
annUnary f a = Ann (ann a) Nil (f a)

annBinary :: (Ann Expr -> Ann Expr -> Expr) -> Ann Expr -> Ann Expr -> Ann Expr
annBinary f a b = Ann (ann a <> ann b) Nil (f a b)


newtype Comment = Comment { getComment :: Text }
  deriving (Eq, Show)
