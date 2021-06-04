{-# LANGUAGE GADTs #-}
module Facet.Term
( -- * Term expressions
  Expr(..)
, xlam
, xapp
, xcon
, xstring
, Tuple(..)
, foldTuple
) where

import Data.Bifunctor (bimap)
import Data.Text (Text)
import Facet.Name
import Facet.Pattern
import Facet.Syntax

-- Term expressions

data Expr
  = XVar (Var (LName Index))
  | XLam [(Pattern Name, Expr)]
  | XApp Expr Expr
  | XCon RName [Expr]
  | XString Text
  | XDict [RName :=: Expr]
  | XLet (Pattern Name) Expr Expr
  | XComp [RName :=: Name] Expr -- ^ NB: the first argument is a specialization of @'Pattern' 'Name'@ to the 'PDict' constructor
  deriving (Eq, Ord, Show)

xlam :: [(T (Pattern Name) a, T Expr b)] -> T Expr (a -> b)
xlam ps = T (XLam (map (bimap getT getT) ps))

xapp :: T Expr (a -> b) -> T Expr a -> T Expr b
xapp (T f) (T a) = T (f `XApp` a)

infixl 9 `xapp`

xcon :: RName -> Tuple (T Expr) ts -> T Expr ts
xcon n b = T (XCon n (foldTuple (pure . getT) b))

xstring :: Text -> T Expr Text
xstring = T . XString


data Tuple f ts where
  None :: Tuple f ()
  (:<) :: f t -> Tuple f ts -> Tuple f (t, ts)

foldTuple :: Monoid m => (forall t . f t -> m) -> Tuple f ts -> m
foldTuple alg = \case
  None    -> mempty
  t :< ts -> alg t <> foldTuple alg ts
