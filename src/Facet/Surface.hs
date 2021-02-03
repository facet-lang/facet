{-# LANGUAGE UndecidableInstances #-}
module Facet.Surface
( -- * Types
  Type(..)
  -- * Expressions
, Expr(..)
, Interface(..)
, Clause(..)
  -- * Patterns
, ValPattern(..)
, EffPattern(..)
  -- * Declarations
, Decl(..)
, Def(..)
  -- * Modules
, Module(..)
, Import(..)
  -- * Annotations
, Ann(..)
, ann_
, comments_
, out_
, annUnary
, annBinary
, Comment(..)
) where

import Control.Lens (Lens, Lens', lens)
import Data.Function (on)
import Data.Text (Text)
import Facet.Name
import Facet.Span
import Facet.Stack
import Facet.Syntax

-- Types

data Type
  = TVar (Q Name)
  | KType
  | KInterface
  | TString
  | TForAll Name (Ann Type) (Ann Type)
  | TArrow (Either Name [Ann Interface]) (Ann Type) (Ann Type)
  | TComp [Ann Interface] (Ann Type)
  | TApp (Ann Type) (Ann Type)
  deriving (Eq, Show)


-- Expressions

data Expr
  = Var (Q Name)
  | Hole Name
  | Lam [Clause]
  | Thunk (Ann Expr)
  | Force (Ann Expr)
  | App (Ann Expr) (Ann Expr)
  | As (Ann Expr) (Ann Type)
  | String Text
  deriving (Eq, Show)


data Interface = Interface (Ann (Q Name)) (Stack (Ann Type))
  deriving (Eq, Show)


data Clause = Clause (Ann EffPattern) (Ann Expr)
  deriving (Eq, Show)


-- Patterns

data ValPattern
  = PWildcard
  | PVar Name
  | PCon (Q Name) [Ann ValPattern]
  deriving (Eq, Show)


data EffPattern
  = PEff (Q Name) [Ann ValPattern] Name
  -- | Catch-all effect pattern. Matches values and effect operations.
  | PAll Name
  | PVal (Ann ValPattern)
  deriving (Eq, Show)


-- Declarations

data Decl = Decl (Ann Type) Def
  deriving (Eq, Show)


data Def
  = DataDef [Ann (Name ::: Ann Type)]
  | InterfaceDef [Ann (Name ::: Ann Type)]
  | TermDef (Ann Expr)
  deriving (Eq, Show)


-- Modules

data Module = Module
  { name      :: MName
  , imports   :: [Ann Import]
  -- FIXME: store source references for operators’ definitions, for error reporting
  , operators :: [(Op, Assoc)]
  , defs      :: [Ann (Name, Ann Decl)]
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

instance HasSpan (Ann a) where
  span_ = ann_

ann_ :: Lens' (Ann a) Span
ann_ = lens ann (\ a ann -> a{ ann })

comments_ :: Lens' (Ann a) (Stack (Span, Comment))
comments_ = lens comments (\ a comments -> a{ comments })

out_ :: Lens (Ann a) (Ann b) a b
out_ = lens out (\ a out -> a{ out })


annUnary :: (Ann a -> a) -> Ann a -> Ann a
annUnary f a = Ann (ann a) Nil (f a)

annBinary :: (Ann a -> Ann b -> a) -> Ann a -> Ann b -> Ann a
annBinary f a b = Ann (ann a <> ann b) Nil (f a b)


newtype Comment = Comment { getComment :: Text }
  deriving (Eq, Show)
