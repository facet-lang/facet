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
import           Facet.Syntax

-- Terms

data Term
  = Var (Var (LName Level))
  | MuR Name (Coterm -> Command)
  | FunR [(Pattern Name, Pattern (Name :=: Term) -> Term)]
  | ConR RName [Term]
  | StringR Text
  | DictR [RName :=: Term]
  | CompR [RName :=: Name] (Pattern (Name :=: Term) -> Term)


-- Coterms

data Coterm
  = Covar (Var (LName Level))
  | MuL Name (Term -> Command)
  | FunL Term Coterm


-- Commands

data Command = Term :|: Coterm


instance Class.Term Term Coterm Command where
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

  (|||) = (:|:)


instance Quote Term XTerm where
  quote d = \case
    Var v     -> XVar (toIndexed d v)
    MuR n b   -> XMuR n (quoteBinder (Covar . Free . (`LName` n) . getUsed) d b)
    FunR ps   -> XFunR (map (uncurry clause) ps)
    ConR n fs -> XConR n (map (quote d) fs)
    StringR t -> XStringR t
    DictR ops -> XDictR (map (fmap (quote d)) ops)
    CompR i b -> XCompR i (snd (clause (PDict i) b))
    where
    var d n = Var (Free (LName (getUsed d) n))
    clause p b = let (d', p') = mapAccumL (\ d n -> (succ d, n :=: var d n)) d p in (p, quote d' (b p'))

instance Quote Coterm XCoterm where
  quote d = \case
    Covar v  -> XCovar (toIndexed d v)
    MuL n b  -> XMuL n (quoteBinder (Var . Free . (`LName` n) . getUsed) d b)
    FunL a b -> XFunL (quote d a) (quote d b)

instance Quote Command XCommand where
  quote d (term :|: coterm) = quote d term :||: quote d coterm


-- Expressions

data XTerm
  = XVar (Var (LName Index))
  | XMuR Name XCommand
  | XFunR [(Pattern Name, XTerm)]
  | XConR RName [XTerm]
  | XStringR Text
  | XDictR [RName :=: XTerm]
  | XCompR [RName :=: Name] XTerm

data XCoterm
  = XCovar (Var (LName Index))
  | XMuL Name XCommand
  | XFunL XTerm XCoterm

data XCommand = XTerm :||: XCoterm
