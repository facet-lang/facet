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
  | MuR (Coterm -> Command)
  | FunR [(Pattern Name, Pattern (Name :=: Term) -> Term)]
  | SumR Int Term
  | PrdR [Term]
  | ConR RName [Term]
  | StringR Text
  | DictR [RName :=: Term]
  | CompR [RName :=: Name] (Pattern (Name :=: Term) -> Term)


-- Coterms

data Coterm
  = Covar (Var (LName Level))
  | MuL (Term -> Command)
  | FunL Term Coterm
  | SumL [Term -> Command]
  | PrdL Int Coterm


-- Commands

data Command = Term :|: Coterm


instance Class.Sequent Term Coterm Command where
  var = Var
  µR = MuR
  funR = FunR
  sumR = SumR
  prdR = PrdR
  conR = ConR
  stringR = StringR
  dictR = DictR
  compR = CompR

  covar = Covar
  µL = MuL
  funL = FunL
  sumL = SumL
  prdL = PrdL

  (.|.) = (:|:)


instance Quote Term X.Term where
  quote = \case
    Var v     -> Quoter (\ d -> X.Var (toIndexed d v))
    MuR b     -> X.MuR <$> quoteBinder (Quoter (\ d -> Covar (Free (LName (getUsed d) __)))) b
    FunR ps   -> X.FunR <$> traverse (uncurry clause) ps
    SumR i t  -> X.SumR i <$> quote t
    PrdR fs   -> X.PrdR <$> traverse quote fs
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
    MuL b    -> X.MuL <$> quoteBinder (Quoter (\ d -> Var (Free (LName (getUsed d) __)))) b
    FunL a b -> liftA2 X.FunL (quote a) (quote b)
    SumL cs  -> X.SumL <$> traverse (quoteBinder (Quoter (\ d -> Var (Free (LName (getUsed d) __))))) cs
    PrdL i k -> X.PrdL i <$> quote k


instance Quote Command X.Command where
  quote (t :|: c) = liftA2 (X.:|:) (quote t) (quote c)
