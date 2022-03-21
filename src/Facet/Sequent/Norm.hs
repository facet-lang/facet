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
  | PrdR [Term]
  | StringR Text


-- Coterms

data Coterm
  = Covar (Var Level)
  | MuL (Term -> Command)
  | LamL Term Coterm
  | SumL (Term -> Command) (Term -> Command)
  | PrdL Int ([Term] -> Command)


-- Commands

data Command = Term :|: Coterm


instance Class.Sequent Term Coterm Command where
  var = Var
  µR = MuR
  lamR = LamR
  sumR1 = SumR1
  sumR2 = SumR2
  prdR = PrdR
  stringR = StringR

  covar = Covar
  µL = MuL
  lamL = LamL
  sumL = SumL
  prdL = PrdL

  (.|.) = (:|:)


instance Quote Term X.Term where
  quote = \case
    Var v     -> Quoter (\ d -> X.Var (toIndexed d v))
    MuR b     -> X.MuR <$> quoteBinder (Quoter (Covar . Free . getUsed)) b
    LamR b    -> X.LamR <$> Quoter (\ d -> runQuoter (d + 2) (quote (b (Var (Free (getUsed d))) (Covar (Free (getUsed (d + 1)))))))
    SumR1 t   -> X.SumR1 <$> quote t
    SumR2 t   -> X.SumR2 <$> quote t
    PrdR fs   -> X.PrdR <$> traverse quote fs
    StringR t -> pure (X.StringR t)

var :: Used -> Term
var = Var . Free . getUsed


instance Quote Coterm X.Coterm where
  quote = \case
    Covar v  -> Quoter (\ d -> X.Covar (toIndexed d v))
    MuL b    -> X.MuL <$> quoteBinder (Quoter var) b
    LamL a b -> liftA2 X.LamL (quote a) (quote b)
    SumL l r -> X.SumL <$> quoteBinder (Quoter var) l <*> quoteBinder (Quoter var) r
    PrdL n k -> X.PrdL n <$> quoteBinder (Quoter (\ d -> map (var .  (d +) . fromIntegral) [0..n])) k


instance Quote Command X.Command where
  quote (t :|: c) = liftA2 (X.:|:) (quote t) (quote c)
