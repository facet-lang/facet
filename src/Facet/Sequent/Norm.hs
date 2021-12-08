module Facet.Sequent.Norm
( -- * Terms
  Term(..)
  -- * Coterms
, Coterm(..)
  -- * Commands
, Command(..)
) where

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


instance Class.Term Term Coterm where
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

  (|||) = (Class.:|:)


instance Quote Term X.Term where
  quote d = \case
    Var v     -> X.Var (toIndexed d v)
    MuR n b   -> X.MuR n (quoteBinder (Covar . Free . (`LName` n) . getUsed) d b)
    FunR ps   -> X.FunR (map (uncurry clause) ps)
    ConR n fs -> X.ConR n (map (quote d) fs)
    StringR t -> X.StringR t
    DictR ops -> X.DictR (map (fmap (quote d)) ops)
    CompR i b -> X.CompR i (snd (clause (PDict i) b))
    where
    var d n = Var (Free (LName (getUsed d) n))
    clause p b = let (d', p') = mapAccumL (\ d n -> (succ d, n :=: var d n)) d p in (p, quote d' (b p'))

instance Quote Coterm X.Coterm where
  quote d = \case
    Covar v  -> X.Covar (toIndexed d v)
    MuL n b  -> X.MuL n (quoteBinder (Var . Free . (`LName` n) . getUsed) d b)
    FunL a b -> X.FunL (quote d a) (quote d b)