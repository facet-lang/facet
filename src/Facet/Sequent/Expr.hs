module Facet.Sequent.Expr
( -- * Terms
  Term(..)
  -- * Coterms
, Coterm(..)
  -- * Commands
, Command(..)
  -- * Interpretation
, interpretTerm
, interpretCoterm
, interpretCommand
) where

import           Control.Applicative (liftA2)
import           Data.Text (Text)
import           Data.Traversable (mapAccumL)
import           Facet.Env
import           Facet.Name
import           Facet.Pattern
import           Facet.Quote
import qualified Facet.Sequent.Class as C
import           Facet.Syntax

-- Terms

data Term
  = Var (Var (LName Index))
  | MuR Command
  | FunR [(Pattern Name, Term)]
  | SumR RName Term
  | PrdR [Term]
  | StringR Text


-- Coterms

data Coterm
  = Covar (Var (LName Index))
  | MuL Command
  | FunL Term Coterm
  | SumL [Command]
  | PrdL Int Command


-- Commands

data Command = Term :|: Coterm


instance C.Sequent (Quoter Term) (Quoter Coterm) (Quoter Command) where
  var v = Quoter (\ d -> Var (toIndexed d v))
  µR b = MuR <$> binder (\ d' -> Quoter (\ d -> covar __ (toIndexed d d'))) b
  funR ps = FunR <$> traverse (uncurry clause) ps
  sumR = fmap . SumR
  prdR = fmap PrdR . sequenceA
  stringR = pure . StringR

  covar v = Quoter (\ d -> Covar (toIndexed d v))
  µL b = MuL <$> binder (\ d' -> Quoter (\ d -> var __ (toIndexed d d'))) b
  funL a b = FunL <$> a <*> b
  sumL = fmap SumL . traverse (binder (\ d' -> Quoter (\ d -> var __ (toIndexed d d'))))
  prdL i b = PrdL i <$> binderN i (\ d' -> Quoter (\ d -> var __ (toIndexed d d'))) b

  (.|.) = liftA2 (:|:)

var :: Name -> Index -> Term
var n i = Var (Free (LName i n))

covar :: Name -> Index -> Coterm
covar n i = Covar (Free (LName i n))

clause :: Pattern Name -> (Pattern (Name :=: Quoter Term) -> Quoter Term) -> Quoter (Pattern Name, Term)
clause p b = Quoter (\ d -> let (d', p') = mapAccumL (\ d' n -> (succ d', n :=: Quoter (\ d -> var n (toIndexed d (getUsed d'))))) d p in (p, runQuoter d' (b p')))


interpretTerm :: C.Sequent t c d => Env t -> Env c -> Term -> t
interpretTerm _G _D = \case
  Var (Free n)   -> _G `index` n
  Var (Global n) -> C.var (Global n)
  MuR b          -> C.µR (\ k -> interpretCommand _G (_D |> PVar (__ :=: k)) b)
  FunR cs        -> C.funR (map (fmap (\ t p -> interpretTerm (_G |> p) _D t)) cs)
  SumR i t       -> C.sumR i (interpretTerm _G _D t)
  PrdR fs        -> C.prdR (map (interpretTerm _G _D) fs)
  StringR s      -> C.stringR s

interpretCoterm :: C.Sequent t c d => Env t -> Env c -> Coterm -> c
interpretCoterm _G _D = \case
  Covar (Free n)   -> _D `index` n
  Covar (Global n) -> C.covar (Global n)
  MuL b            -> C.µL (\ t -> interpretCommand (_G |> PVar (__ :=: t)) _D b)
  FunL a k         -> C.funL (interpretTerm _G _D a) (interpretCoterm _G _D k)
  SumL cs          -> C.sumL (map (\ d t -> interpretCommand (_G |> PVar (__ :=: t)) _D d) cs)
  PrdL i c         -> C.prdL i (\ cs -> interpretCommand (foldl (\ e c -> e |> PVar (__ :=: c)) _G cs) _D c)

interpretCommand :: C.Sequent t c d => Env t -> Env c -> Command -> d
interpretCommand _G _D (t :|: c) = interpretTerm _G _D t C..|. interpretCoterm _G _D c
