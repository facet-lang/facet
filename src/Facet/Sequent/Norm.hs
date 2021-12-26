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
  | FunR (Term -> Term)
  | SumR RName Term
  | PrdR [Term]
  | StringR Text


-- Coterms

data Coterm
  = Covar (Var Level)
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
    MuR b     -> X.MuR <$> quoteBinder (Quoter (Covar . Free . getUsed)) b
    FunR b    -> X.FunR <$> quoteBinder (Quoter (Var . Free . getUsed)) b
    SumR i t  -> X.SumR i <$> quote t
    PrdR fs   -> X.PrdR <$> traverse quote fs
    StringR t -> pure (X.StringR t)

var :: Used -> Term
var = Var . Free . getUsed


instance Quote Coterm X.Coterm where
  quote = \case
    Covar v  -> Quoter (\ d -> X.Covar (toIndexed d v))
    MuL b    -> X.MuL <$> quoteBinder (Quoter var) b
    FunL a b -> liftA2 X.FunL (quote a) (quote b)
    SumL cs  -> X.SumL <$> traverse (quoteBinder (Quoter var)) cs
    PrdL n k -> X.PrdL n <$> quoteBinder (Quoter (\ d -> map (var .  (d +) . fromIntegral) [0..n])) k


instance Quote Command X.Command where
  quote (t :|: c) = liftA2 (X.:|:) (quote t) (quote c)
