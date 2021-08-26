module Facet.Term.Expr
( -- * Term expressions
  Term(..)
, TExpr(..)
, Fields(..)
) where

import Data.Bifunctor (bimap)
import Data.Text (Text)
import Facet.Name
import Facet.Pattern
import Facet.Syntax

-- Term expressions

data Term
  = Var (Var (LName Index))
  | Lam [(Pattern Name, Term)]
  | App Term Term
  | Con RName [Term]
  | String Text
  | Dict [RName :=: Term]
  | Let (Pattern Name) Term Term
  | Comp [RName :=: Name] Term -- ^ NB: the first argument is a specialization of @'Pattern' 'Name'@ to the 'PDict' constructor
  deriving (Eq, Ord, Show)

class TExpr expr where
  xvar :: T (Var (LName Index)) a -> expr a

  xlam :: [(T (Pattern Name) a, expr b)] -> expr (a -> b)

  xapp :: expr (a -> b) -> expr a -> expr b

  infixl 9 `xapp`

  xcon :: Fields expr fs => RName -> fs -> expr fs

  xstring :: Text -> expr Text

  xlet :: T (Pattern Name) t -> expr t -> expr u -> expr u

instance TExpr (T Term) where
  xvar = T . Var . getT

  xlam ps = T (Lam (map (bimap getT getT) ps))

  xapp (T f) (T a) = T (f `App` a)

  xcon n b = T (Con n (foldFields (pure . getT) b))

  xstring = T . String

  xlet (T p) (T v) (T b) = T (Let p v b)


class Fields f fs where
  foldFields :: Monoid m => (forall t . f t -> m) -> fs -> m

instance Fields f () where
  foldFields _ _ = mempty

instance Fields f fs => Fields f (f t, fs) where
  foldFields alg = mappend . alg . fst <*> foldFields alg . snd
