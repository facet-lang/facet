{-# LANGUAGE GADTs #-}
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
import           Data.Void (Void)
import qualified Facet.Core.Type as T
import           Facet.Name
import           Facet.Snoc
import           Facet.Syntax

-- Patterns

data ValuePattern a
  = PWildcard
  | PVar a
  | PCon QName (Snoc (ValuePattern a))
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data EffectPattern a
  = PAll a
  | POp QName (Snoc (ValuePattern a)) a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Pattern a
  = PEff (EffectPattern a)
  | PVal (ValuePattern a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

pvar :: a -> Pattern a
pvar = PVal . PVar

pcon :: QName -> Snoc (ValuePattern a) -> Pattern a
pcon n fs = PVal $ PCon n fs

peff :: QName -> Snoc (ValuePattern a) -> a -> Pattern a
peff o vs k = PEff $ POp o vs k


fill :: Traversable t => (b -> (b, c)) -> b -> t a -> (b, t c)
fill f = mapAccumL (const . f)


-- Term expressions

data Expr u where
  XTLam :: Expr N -> Expr N
  XInst :: Expr N -> T.TExpr P -> Expr N
  XLam :: [(Pattern Name, Expr N)] -> Expr N
  XApp :: Expr N -> Expr P -> Expr N
  XOp :: QName -> Snoc (T.TExpr P) -> Snoc (Expr P) -> Expr N
  XForce :: Expr P -> Expr N
  XReturn :: Expr P -> Expr N
  -- | Evaluates the first operand, and then evaluates the second providing the value returned by the first as a variable in the environment.
  XBind :: Expr N -> Expr N -> Expr N
  XVar :: Var Void Index -> Expr P
  XCon :: QName -> Snoc (T.TExpr P) -> Snoc (Expr P) -> Expr P
  XString :: Text -> Expr P
  XThunk :: Expr N -> Expr P

deriving instance Eq   (Expr u)
deriving instance Ord  (Expr u)
deriving instance Show (Expr u)
