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
  | SumR RName Term
  | PrdR [Term]
  | StringR Text


-- Coterms

data Coterm
  = Covar (Var (LName Level))
  | MuL (Term -> Command)
  | FunL Term Coterm
  | SumL [Term -> Command]
  | PrdL Int ([Term] -> Command)


-- Commands

data Command = Term :|: Coterm


instance Class.Sequent Term Coterm Command where
  var = Var
  µR = MuR
  funR = FunR
  sumR = SumR
  prdR = PrdR
  stringR = StringR

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
    StringR t -> pure (X.StringR t)
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
    PrdL n k -> X.PrdL n <$> quoteBinder (Quoter (\ d -> map (\ d' -> Var (Free (LName (getUsed d + fromIntegral d') __))) [0..n])) k


instance Quote Command X.Command where
  quote (t :|: c) = liftA2 (X.:|:) (quote t) (quote c)
