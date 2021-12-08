module Facet.Sequent.Expr
( -- * Terms
  Term(..)
  -- * Coterms
, Coterm(..)
  -- * Commands
, (C.:|:)(..)
) where

import           Data.Bitraversable (bisequenceA)
import           Data.Text (Text)
import           Data.Traversable (mapAccumL)
import           Facet.Name
import           Facet.Pattern
import           Facet.Quote
import qualified Facet.Sequent.Class as C
import           Facet.Syntax

-- Terms

data Term
  = Var (Var (LName Index))
  | MuR Name (Term C.:|: Coterm)
  | FunR [(Pattern Name, Term)]
  | ConR RName [Term]
  | StringR Text
  | DictR [RName :=: Term]
  | CompR [RName :=: Name] Term


-- Coterms

data Coterm
  = Covar (Var (LName Index))
  | MuL Name (Term C.:|: Coterm)
  | FunL Term Coterm


instance C.Term (Quoter Term) (Quoter Coterm) where
  var v = Quoter (\ d -> Var (toIndexed d v))
  µR n b = MuR n <$> binder (\ d d' -> covar n (toIndexed d d')) (bisequenceA . b)
  funR ps = FunR <$> traverse (uncurry clause) ps
  conR n fs = ConR n <$> sequenceA fs
  stringR = pure . StringR
  dictR i = DictR <$> traverse sequenceA i
  compR i b = CompR i . snd <$> clause (PDict i) b

  covar v = Quoter (\ d -> Covar (toIndexed d v))
  µL n b = MuL n <$> binder (\ d d' -> var n (toIndexed d d')) (bisequenceA . b)
  funL a b = FunL <$> a <*> b

  (|||) = (C.:|:)

var :: Name -> Index -> Term
var n i = Var (Free (LName i n))

covar :: Name -> Index -> Coterm
covar n i = Covar (Free (LName i n))

clause :: Pattern Name -> (Pattern (Name :=: Quoter Term) -> Quoter Term) -> Quoter (Pattern Name, Term)
clause p b = Quoter (\ d -> let (d', p') = mapAccumL (\ d' n -> (succ d', n :=: Quoter (\ d -> var n (toIndexed d (getUsed d'))))) d p in (p, runQuoter d' (b p')))
