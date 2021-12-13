module Facet.Sequent.Norm
( -- * Terms
  Term(..)
  -- * Coterms
, Coterm(..)
  -- * Commands
, Command(..)
) where

import           Control.Applicative (liftA2)
import           Data.Text (Text)
import           Data.Traversable (mapAccumL)
import           Facet.Name
import           Facet.Pattern
import           Facet.Quote
import qualified Facet.Sequent.Class as Class
import qualified Facet.Sequent.Expr as X
import           Facet.Syntax

-- Terms

data Term
  = Var (Var (LName Level))
  | MuR Name (Coterm -> Term Class.:|: Coterm)
  | FunR [(Pattern Name, Pattern (Name :=: Term) -> Term)]
  | ConR RName [Term]
  | StringR Text
  | DictR [RName :=: Term]
  | CompR [RName :=: Name] (Pattern (Name :=: Term) -> Term)


-- Coterms

data Coterm
  = Covar (Var (LName Level))
  | MuL Name (Term -> Term Class.:|: Coterm)
  | FunL Term Coterm


-- Commands

data Command = Term :|: Coterm


instance Class.Sequent Term Coterm (Term Class.:|: Coterm) where
  var = Var
  µR = MuR
  funR = FunR
  conR = ConR
  stringR = StringR
  dictR = DictR
  compR = CompR

  covar = Covar
  µL = MuL
  funL = FunL

  (.|.) = (Class.:|:)


instance Quote Term X.Term where
  quote = \case
    Var v     -> Quoter (\ d -> X.Var (toIndexed d v))
    MuR n b   -> X.MuR n <$> quoteBinder (Quoter (\ d -> Covar (Free (LName (getUsed d) n)))) b
    FunR ps   -> X.FunR <$> traverse (uncurry clause) ps
    ConR n fs -> X.ConR n <$> traverse quote fs
    StringR t -> pure (X.StringR t)
    DictR ops -> X.DictR <$> traverse (traverse quote) ops
    CompR i b -> X.CompR i . snd <$> clause (PDict i) b
    where
    var d n = Var (Free (LName (getUsed d) n))
    clause :: Pattern Name -> (Pattern (Name :=: Term) -> Term) -> Quoter (Pattern Name, X.Term)
    clause p b = Quoter (\ d -> let (_, p') = mapAccumL (\ d' n -> (succ d', n :=: var d' n)) d p in (p, runQuoter d (quote (b p'))))


instance Quote Coterm X.Coterm where
  quote = \case
    Covar v  -> Quoter (\ d -> X.Covar (toIndexed d v))
    MuL n b  -> X.MuL n <$> quoteBinder (Quoter (\ d -> Var (Free (LName (getUsed d) n)))) b
    FunL a b -> liftA2 X.FunL (quote a) (quote b)
