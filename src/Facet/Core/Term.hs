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
  -- ** Positive term constructors
, varE
, conE
, stringE
, thunkE
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

data Expr
  = XTLam Expr
  | XInst Expr T.TExpr
  | XLam [(Pattern Name, Expr)]
  | XApp Expr Expr
  | XOp QName (Snoc T.TExpr) (Snoc Expr)
  | XForce Expr
  | XReturn Expr
  -- | Evaluates the first operand, and then evaluates the second providing the value returned by the first as a variable in the environment.
  | XBind Expr Expr
  | XVar (Var Void Index)
  | XCon QName (Snoc T.TExpr) (Snoc Expr)
  | XString Text
  | XThunk Expr
  deriving (Eq, Ord, Show)


-- Positive term constructors

varE :: Var Void Index -> Pos Expr
varE v = Pos' (XVar v)

conE :: QName -> Snoc T.TExpr -> Snoc (Pos Expr) -> Pos Expr
conE n ts fs = Pos' (XCon n ts ((\ (Pos' e) -> e) <$> fs))

stringE :: Text -> Pos Expr
stringE s = Pos' (XString s)

thunkE :: Neg Expr -> Pos Expr
thunkE (Neg' e) = Pos' (XThunk e)
