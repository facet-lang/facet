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
, CExpr(..)
, VExpr(..)
) where

import           Data.Text (Text)
import           Data.Traversable (mapAccumL)
import           Data.Void (Void)
import qualified Facet.Core.Type as T
import           Facet.Name
import           Facet.Snoc
import           Facet.Syntax

-- Patterns

data ValuePattern a
  = PWildcard
  | PVar a
  | PCon (Q Name) (Snoc (ValuePattern a))
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data EffectPattern a
  = PAll a
  | POp (Q Name) (Snoc (ValuePattern a)) a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Pattern a
  = PEff (EffectPattern a)
  | PVal (ValuePattern a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

pvar :: a -> Pattern a
pvar = PVal . PVar

pcon :: Q Name -> Snoc (ValuePattern a) -> Pattern a
pcon n fs = PVal $ PCon n fs

peff :: Q Name -> Snoc (ValuePattern a) -> a -> Pattern a
peff o vs k = PEff $ POp o vs k


fill :: Traversable t => (b -> (b, c)) -> b -> t a -> (b, t c)
fill f = mapAccumL (const . f)


-- Term expressions

data Expr
  = XVar (Var Void Index)
  | XTLam Expr
  | XInst Expr T.TExpr
  | XLam [(Pattern Name, Expr)]
  | XApp Expr Expr
  | XCon (Q Name) (Snoc T.TExpr) (Snoc Expr)
  | XString Text
  | XOp (Q Name) (Snoc T.TExpr) (Snoc Expr)
  deriving (Eq, Ord, Show)

data CExpr
  = CXTLam CExpr
  | CXInst CExpr T.TExpr
  | CXLam [(Pattern Name, CExpr)]
  | CXApp CExpr VExpr
  | CXOp (Q Name) (Snoc T.TExpr) (Snoc VExpr)
  deriving (Eq, Ord, Show)

data VExpr
  = VXVar (Var Void Index)
  | VXCon (Q Name) (Snoc T.TExpr) (Snoc VExpr)
  | VXString Text
  deriving (Eq, Ord, Show)
