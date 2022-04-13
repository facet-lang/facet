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
import           Facet.Name
import           Facet.Quote
import qualified Facet.Sequent.Class as Class
import qualified Facet.Sequent.Expr as X
import           Facet.Syntax

-- Terms

data Term
  = Var (Var Level)
  | MuR (Coterm -> Command)
  | LamR (Term -> Coterm -> Command)
  | SumR Int Term
  | BottomR Command
  | UnitR
  | PrdR Term Term
  | StringR Text


-- Coterms

data Coterm
  = Covar (Var Level)
  | MuL (Term -> Command)
  | LamL Term Coterm
  | SumL [Coterm]
  | UnitL
  | PrdL1 Coterm
  | PrdL2 Coterm


-- Commands

data Command
  = Term :|: Coterm
  | Let Term (Term -> Command)


instance Class.Sequent Term Coterm Command where
  var = Var
  µR = MuR
  lamR = LamR
  sumR = SumR
  bottomR = BottomR
  unitR = UnitR
  prdR = PrdR
  stringR = StringR

  covar = Covar
  µL = MuL
  lamL = LamL
  sumL = SumL
  unitL = UnitL
  prdL1 = PrdL1
  prdL2 = PrdL2

  (.|.) = (:|:)
  let' = Let


instance Quote Term X.Term where
  quote = \case
    Var v     -> Quoter (\ d -> X.Var (toIndexed d v))
    MuR b     -> X.MuR <$> quoteBinder (Quoter (Covar . Free)) b
    LamR b    -> X.LamR <$> Quoter (\ d -> runQuoter (d + 2) (quote (b (Var (Free d)) (Covar (Free (d + 1))))))
    SumR i t  -> X.SumR i <$> quote t
    BottomR c -> X.BottomR <$> quote c
    UnitR     -> pure X.UnitR
    PrdR l r  -> X.PrdR <$> quote l <*> quote r
    StringR t -> pure (X.StringR t)

var :: Level -> Term
var = Var . Free


instance Quote Coterm X.Coterm where
  quote = \case
    Covar v  -> Quoter (\ d -> X.Covar (toIndexed d v))
    MuL b    -> X.MuL <$> quoteBinder (Quoter var) b
    LamL a b -> liftA2 X.LamL (quote a) (quote b)
    SumL cs  -> X.SumL <$> traverse quote cs
    UnitL    -> pure X.UnitL
    PrdL1 k  -> X.PrdL1 <$> quote k
    PrdL2 k  -> X.PrdL2 <$> quote k


instance Quote Command X.Command where
  quote (t :|: c) = liftA2 (X.:|:) (quote t) (quote c)
  quote (Let t b) = X.Let <$> quote t <*> quoteBinder (Quoter var) b
