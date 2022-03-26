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
  | SumR1 Term
  | SumR2 Term
  | UnitR
  | PrdR Term Term
  | StringR Text


-- Coterms

data Coterm
  = Covar (Var Level)
  | MuL (Term -> Command)
  | LamL Term Coterm
  | SumL Coterm Coterm
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
  sumR1 = SumR1
  sumR2 = SumR2
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
    MuR b     -> X.MuR <$> quoteBinder (Quoter (Covar . Free . getUsed)) b
    LamR b    -> X.LamR <$> Quoter (\ d -> runQuoter (d + 2) (quote (b (Var (Free (getUsed d))) (Covar (Free (getUsed (d + 1)))))))
    SumR1 t   -> X.SumR1 <$> quote t
    SumR2 t   -> X.SumR2 <$> quote t
    UnitR     -> pure X.UnitR
    PrdR l r  -> X.PrdR <$> quote l <*> quote r
    StringR t -> pure (X.StringR t)

var :: Used -> Term
var = Var . Free . getUsed


instance Quote Coterm X.Coterm where
  quote = \case
    Covar v  -> Quoter (\ d -> X.Covar (toIndexed d v))
    MuL b    -> X.MuL <$> quoteBinder (Quoter var) b
    LamL a b -> liftA2 X.LamL (quote a) (quote b)
    SumL l r -> X.SumL <$> quote l <*> quote r
    UnitL    -> pure X.UnitL
    PrdL1 k  -> X.PrdL1 <$> quote k
    PrdL2 k  -> X.PrdL2 <$> quote k


instance Quote Command X.Command where
  quote (t :|: c) = liftA2 (X.:|:) (quote t) (quote c)
  quote (Let t b) = X.Let <$> quote t <*> quoteBinder (Quoter var) b
