module Facet.Term
( -- * Term expressions
  Expr(..)
, xlam
, xapp
, xcon
, xstring
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

xcon :: Fields (T Expr) fs => RName -> fs -> T Expr fs
xcon n b = T (XCon n (foldFields (pure . getT) b))

xstring :: Text -> T Expr Text
xstring = T . XString


class Fields f fs where
  foldFields :: Monoid m => (forall t . f t -> m) -> fs -> m

instance Fields f () where
  foldFields _ _ = mempty

instance Fields f fs => Fields f (f t, fs) where
  foldFields alg = mappend . alg . fst <*> foldFields alg . snd
