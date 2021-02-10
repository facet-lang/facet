module Facet.Core.Term
( -- * Patterns
  ValuePattern(..)
, EffectPattern(..)
, Pattern(..)
, pvar
, pcon
, fill
  -- * Term expressions
, Expr(..)
) where

import           Data.Text (Text)
import           Data.Traversable (mapAccumL)
import           Data.Void (Void)
import qualified Facet.Core.Type as T
import           Facet.Name
import           Facet.Stack
import           Facet.Syntax

-- Patterns

data ValuePattern a
  = PWildcard
  | PVar a
  | PCon (Q Name) (Stack (ValuePattern a))
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data EffectPattern a = POp (Q Name) (Stack (ValuePattern a)) a

data Pattern a
  = PEff (Q Name) (Stack (ValuePattern a)) a
  | PVal (ValuePattern a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

pvar :: a -> Pattern a
pvar = PVal . PVar

pcon :: Q Name -> Stack (ValuePattern a) -> Pattern a
pcon n fs = PVal $ PCon n fs


fill :: Traversable t => (b -> (b, c)) -> b -> t a -> (b, t c)
fill f = mapAccumL (const . f)


-- Term expressions

data Expr
  = XVar (Var Void Index)
  | XTLam Expr
  | XLam [(Pattern Name, Expr)]
  | XInst Expr T.TExpr
  | XApp Expr Expr
  | XCon (Q Name) (Stack T.TExpr) (Stack Expr)
  | XString Text
  | XOp (Q Name) (Stack T.TExpr) (Stack Expr)
  deriving (Eq, Ord, Show)
