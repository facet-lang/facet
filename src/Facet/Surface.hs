module Facet.Surface
( -- * Expressions
  Expr(..)
, Type
, free
, qual
, Binding(..)
, Delta(..)
, Sig(..)
, ($$)
, Comp(..)
, Pattern(..)
  -- * Declarations
, Decl(..)
, Def(..)
  -- * Modules
, Module(..)
, Import(..)
  -- * Annotations
, Ann(..)
, Comment(..)
) where

import Data.Function (on)
import Data.List.NonEmpty (NonEmpty)
import Data.Text (Text)
import Facet.Name
import Facet.Span
import Facet.Stack
import Facet.Syntax hiding (out)

-- Expressions

data Expr
  = Var (Maybe MName) DName
  | Hole UName
  | Type
  | Interface
  | ForAll [Ann Binding] (Ann (Sig (Ann Type)))
  | Comp (Ann Comp)
  | App (Ann Expr) (Ann Expr)
  -- FIXME: tupling/unit should take a list of expressions
  deriving (Eq, Show)

type Type = Expr


free :: DName -> Expr
free = Var Nothing

qual :: QName -> Expr
qual (m :.: n) = Var (Just m) n


data Binding = Binding
  { _pl   :: Pl
  , names :: NonEmpty UName
  , sig   :: Ann (Sig (Ann Expr))
  }
  deriving (Eq, Show)

data Delta = Delta (Ann (Maybe MName, DName)) (Stack (Ann Type))
  deriving (Eq, Show)

-- | Really this is a signature /adjustment/ consisting of the sum of the individual deltas, but “signature” shortens shorter.
data Sig a = Sig
  { delta :: [Ann Delta]
  , type' :: a
  }
  deriving (Eq, Show)


($$) :: Ann Expr -> Ann Expr -> Ann Expr
f $$ a = Ann (ann f <> ann a) Nil (App f a)

infixl 9 $$


data Comp
  = Expr (Ann Expr)
  | Clauses [(NonEmpty (Ann Pattern), Ann Expr)]
  deriving (Eq, Show)


data Pattern
  = PVar UName
  | PCon UName [Ann Pattern]
  | PEff UName [Ann Pattern] UName
  -- FIXME: catch-all effect patterns
  deriving (Eq, Show)


-- Declarations

data Decl = Decl [Ann Binding] (Ann (Sig (Ann Type :=: Def)))
  deriving (Eq, Show)

data Def
  = DataDef [Ann (UName ::: Ann Type)]
  | InterfaceDef [Ann (UName ::: Ann Type)]
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


newtype Comment = Comment { getComment :: Text }
  deriving (Eq, Show)
