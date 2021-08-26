{-# LANGUAGE UndecidableInstances #-}
module Facet.Surface.Expr
( -- * Types
  Kind(..)
, Type(..)
, Mul(..)
  -- * Expressions
, Expr(..)
, Interface(..)
, Clause(..)
  -- * Patterns
, Pattern(..)
, ValPattern(..)
, EffPattern(..)
  -- * Definitions
, Def(..)
  -- * Modules
, Module(..)
, Import(..)
  -- * Annotations
, Ann(..)
, ann_
, context_
, out_
, annUnary
, annBinary
, Comment(..)
) where

import Data.Function (on)
import Data.Text (Text)
import Facet.Name
import Facet.Snoc
import Facet.Span
import Facet.Syntax
import Fresnel.Lens (Lens, Lens', lens)

-- Types

data Kind
  = KType
  | KInterface
  | KArrow (Maybe Name) (Ann Comment Kind) (Ann Comment Kind)
  deriving (Eq, Show)

data Type
  = TVar QName
  | TString
  | TForAll Name (Ann Comment Kind) (Ann Comment Type)
  | TArrow (Maybe Name) (Maybe Mul) (Ann Comment Type) (Ann Comment Type)
  | TComp [Ann Comment Interface] (Ann Comment Type)
  | TApp (Ann Comment Type) (Ann Comment Type)
  deriving (Eq, Show)

data Mul = Zero | One
  deriving (Bounded, Enum, Eq, Ord, Show)


-- Expressions

data Expr
  = Var QName
  | Hole Name
  | Lam [Clause]
  | App (Ann Comment Expr) (Ann Comment Expr)
  | As (Ann Comment Expr) (Ann Comment Type)
  | String Text
  deriving (Eq, Show)


data Interface = Interface (Ann Comment QName) (Snoc (Ann Comment Type))
  deriving (Eq, Show)


data Clause = Clause (Ann Comment Pattern) (Ann Comment Expr)
  deriving (Eq, Show)


-- Patterns

data Pattern
  = PVal (Ann Comment ValPattern)
  | PEff (Ann Comment EffPattern)
  deriving (Eq, Show)

data ValPattern
  = PWildcard
  | PVar Name
  | PCon QName [Ann Comment ValPattern]
  deriving (Eq, Show)

data EffPattern = POp QName [Ann Comment ValPattern] (Ann Comment ValPattern)
  deriving (Eq, Show)


-- Declarations

data Def
  = DataDef [Ann Comment (Name ::: Ann Comment Type)] (Ann Comment Kind)
  | InterfaceDef [Ann Comment (Name ::: Ann Comment Type)] (Ann Comment Kind)
  | TermDef (Ann Comment Expr) (Ann Comment Type)
  deriving (Eq, Show)


-- Modules

data Module = Module
  { name      :: MName
  , imports   :: [Ann Comment Import]
  -- FIXME: store source references for operators’ definitions, for error reporting
  , operators :: [(Op, Assoc)]
  , defs      :: [Ann Comment (Name, Ann Comment Def)]
  }
  deriving (Eq, Show)


newtype Import = Import { name :: MName }
  deriving (Eq, Show)


-- Annotations

data Ann c a = Ann
  { ann     :: Span
  , context :: Snoc (Span, c)
  , out     :: a
  }
  deriving (Foldable, Functor, Traversable)

instance Eq a => Eq (Ann c a) where
  (==) = (==) `on` out

instance Ord a => Ord (Ann c a) where
  compare = compare `on` out

instance Show a => Show (Ann c a) where
  showsPrec p = showsPrec p . out

instance HasSpan (Ann c a) where
  span_ = ann_

ann_ :: Lens' (Ann c a) Span
ann_ = lens ann (\ a ann -> a{ ann })

context_ :: Lens (Ann c a) (Ann d a) (Snoc (Span, c)) (Snoc (Span, d))
context_ = lens context (\ a context -> a{ context })

out_ :: Lens (Ann c a) (Ann c b) a b
out_ = lens out (\ a out -> a{ out })


annUnary :: (Ann c a -> a) -> Ann c a -> Ann c a
annUnary f a = Ann (ann a) Nil (f a)

annBinary :: (Ann c a -> Ann c b -> a) -> Ann c a -> Ann c b -> Ann c a
annBinary f a b = Ann (ann a <> ann b) Nil (f a b)


newtype Comment = Comment { getComment :: Text }
  deriving (Eq, Show)
