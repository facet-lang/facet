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
, Expr'(..)
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

data Expr u
  = XVar (Var Void Index)
  | XTLam (Expr u)
  | XInst (Expr u) (T.TExpr P)
  | XLam [(Pattern Name, Expr u)]
  | XApp (Expr u) (Expr u)
  | XCon (Q Name) (Snoc (T.TExpr P)) (Snoc (Expr u))
  | XString Text
  | XOp (Q Name) (Snoc (T.TExpr P)) (Snoc (Expr u))
  deriving (Eq, Ord, Show)

data Expr' u where
  EXTLam :: Expr' N -> Expr' N
  EXInst :: Expr' N -> T.TExpr P -> Expr' N
  EXLam :: [(Pattern Name, Expr' N)] -> Expr' N
  EXApp :: Expr' N -> Expr' P -> Expr' N
  EXOp :: Q Name -> Snoc (T.TExpr P) -> Snoc (Expr' P) -> Expr' N
  EXForce :: Expr' P -> Expr' N
  EXReturn :: Expr' P -> Expr' N
  -- | Evaluates the first operand, and then evaluates the second providing the value returned by the first as a variable in the environment.
  EXBind :: Expr' N -> Expr' N -> Expr' N
  EXVar :: Var Void Index -> Expr' P
  EXCon :: Q Name -> Snoc (T.TExpr P) -> Snoc (Expr' P) -> Expr' P
  EXString :: Text -> Expr' P
  EXThunk :: Expr' N -> Expr' P

deriving instance Eq   (Expr' u)
deriving instance Ord  (Expr' u)
deriving instance Show (Expr' u)
