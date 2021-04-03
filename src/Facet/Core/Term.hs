module Facet.Core.Term
( -- * Term expressions
  Expr(..)
, T(..)
, xtlam
, xinst
, xlam
, xapp
, xcon
, xstring
) where

import           Control.Arrow ((***))
import           Data.Text (Text)
import           Facet.Core.Pattern
import qualified Facet.Core.Type as T
import           Facet.Name
import           Facet.Syntax

-- Term expressions

data Expr
  = XVar (Var (LName Index))
  | XTLam Name Expr
  | XInst Expr T.TExpr
  | XLam [(Pattern Name, Expr)]
  | XApp Expr Expr
  | XCon RName [Expr]
  | XString Text
  | XDict [RName :=: Expr]
  deriving (Eq, Ord, Show)


newtype T a t = T { getT :: a }

xtlam :: Name -> T Expr b -> T Expr (T.TExpr -> b)
xtlam n (T b) = T (XTLam n b)

xinst :: T Expr (T.TExpr -> b) -> T.TExpr -> T Expr b
xinst (T b) t = T (XInst b t)

xlam :: [(T (Pattern Name) a, T Expr b)] -> T Expr (a -> b)
xlam cs = T (XLam (map (getT *** getT) cs))

xapp :: T Expr (a -> b) -> T Expr a -> T Expr b
xapp (T f) (T a) = T (XApp f a)

xcon :: RName -> [Expr] -> T Expr c
xcon n fs = T (XCon n fs)

xstring :: Text -> T Expr Text
xstring = T . XString
