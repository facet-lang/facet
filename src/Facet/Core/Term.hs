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

data Expr
  = XVar (Var Void Index)
  | XTLam Expr
  | XInst Expr (T.TExpr V)
  | XLam [(Pattern Name, Expr)]
  | XApp Expr Expr
  | XCon (Q Name) (Snoc (T.TExpr V)) (Snoc Expr)
  | XString Text
  | XOp (Q Name) (Snoc (T.TExpr V)) (Snoc Expr)
  deriving (Eq, Ord, Show)

data Expr' u where
  EXTLam :: Expr' C -> Expr' C
  EXInst :: Expr' C -> T.TExpr V -> Expr' C
  EXLam :: [(Pattern Name, Expr' C)] -> Expr' C
  EXApp :: Expr' C -> Expr' V -> Expr' C
  EXOp :: Q Name -> Snoc (T.TExpr V) -> Snoc (Expr' V) -> Expr' C
  EXForce :: Expr' V -> Expr' C
  EXReturn :: Expr' V -> Expr' C
  -- | Evaluates the first operand, and then evaluates the second providing the value returned by the first as a variable in the environment.
  EXBind :: Expr' C -> Expr' C -> Expr' C
  EXVar :: Var Void Index -> Expr' V
  EXCon :: Q Name -> Snoc (T.TExpr V) -> Snoc (Expr' V) -> Expr' V
  EXString :: Text -> Expr' V
  EXThunk :: Expr' C -> Expr' V

deriving instance Eq   (Expr' u)
deriving instance Ord  (Expr' u)
deriving instance Show (Expr' u)
