module Facet.Term.Expr
( -- * Term expressions
  Term(..)
) where

import           Control.Applicative (liftA2)
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
  ($$) = liftA2 App
  dict fs = Dict <$> traverse sequenceA fs
  comp p b = Comp p <$> snd (clause (PDict p) b)

clause :: Traversable t => t Name -> (t (Name :=: Quoter Term) -> Quoter Term) -> (t Name, Quoter Term)
clause p b = (p, Quoter (\ d -> let (_, p') = mapAccumL (\ d n -> (succ d, n :=: Free (LName d n))) d p in runQuoter d (b (fmap C.var <$> p'))))
