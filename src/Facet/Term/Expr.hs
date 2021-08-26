module Facet.Term.Expr
( -- * Term expressions
  Term(..)
, TExpr(..)
, Fields(..)
) where

import           Control.Applicative (liftA2)
import           Data.Bifunctor (bimap)
import           Data.Text (Text)
import           Data.Traversable (mapAccumL)
import           Facet.Name
import           Facet.Pattern
import           Facet.Quote
import           Facet.Syntax
import qualified Facet.Term.Class as C

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

instance C.Term (Quoter Term) where
  string = pure . String
  con n fs = Con n <$> sequenceA fs
  lam b = Lam <$> traverse (sequenceA . uncurry clause) b
  var v = Quoter (\ d -> Var (toIndexed d v))
  app = liftA2 App
  dict fs = Dict <$> traverse sequenceA fs
  comp p b = Comp p <$> snd (clause (PDict p) b)

clause :: Traversable t => t Name -> (t (Name :=: Quoter Term) -> Quoter Term) -> (t Name, Quoter Term)
clause p b = (p, Quoter (\ d -> let (_, p') = mapAccumL (\ d n -> (succ d, n :=: Free (LName d n))) d p in runQuoter (b (fmap C.var <$> p')) d))

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
