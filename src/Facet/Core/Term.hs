module Facet.Core.Term
( -- * Patterns
  ValuePattern(..)
, EffectPattern(..)
, Pattern(..)
, pvar
, pcon
, peff
, fill
  -- * Term expressions
, Expr(..)
) where

import           Data.Text (Text)
import           Data.Traversable (mapAccumL)
import qualified Facet.Core.Type as T
import           Facet.Name
import           Facet.Snoc
import           Facet.Syntax

-- Patterns

data ValuePattern a
  = PWildcard
  | PVar a
  | PCon RName (Snoc (ValuePattern a))
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data EffectPattern a
  = POp RName (Snoc (ValuePattern a)) a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Pattern a
  = PEff (EffectPattern a)
  | PVal (ValuePattern a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

pvar :: a -> Pattern a
pvar = PVal . PVar

pcon :: RName -> Snoc (ValuePattern a) -> Pattern a
pcon n fs = PVal $ PCon n fs

peff :: RName -> Snoc (ValuePattern a) -> a -> Pattern a
peff o vs k = PEff $ POp o vs k


fill :: Traversable t => (b -> (b, c)) -> b -> t a -> (b, t c)
fill f = mapAccumL (const . f)


-- Term expressions

data Expr
  = XVar (Var Index)
  | XTLam Expr
  | XInst Expr T.TExpr
  | XLam [(Pattern Name, Expr)]
  | XApp Expr Expr
  | XCon RName (Snoc T.TExpr) (Snoc Expr)
  | XString Text
  | XOp RName (Snoc T.TExpr) (Snoc Expr)
  deriving (Eq, Ord, Show)
