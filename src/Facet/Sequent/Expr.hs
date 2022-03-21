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
import           Facet.Name
import           Facet.Quote
import qualified Facet.Sequent.Class as C
import           Facet.Syntax

-- Terms

data Term
  = Var (Var Index)
  | MuR Command
  | LamR Command
  | SumR1 Term
  | SumR2 Term
  | PrdR Term Term
  | StringR Text


-- Coterms

data Coterm
  = Covar (Var Index)
  | MuL Command
  | LamL Term Coterm
  | SumL Command Command
  | PrdL1 Command
  | PrdL2 Command


-- Commands

data Command = Term :|: Coterm


instance C.Sequent (Quoter Term) (Quoter Coterm) (Quoter Command) where
  var v = Quoter (\ d -> Var (toIndexed d v))
  µR b = MuR <$> binder (\ d' -> Quoter (\ d -> covar (toIndexed d d'))) b
  lamR b = LamR <$> binder (\ d' -> Quoter (\ d -> var (toIndexed d d'))) (\ t -> binder (\ d'' -> Quoter (\ d -> covar (toIndexed d d''))) (b t))
  sumR1 = fmap SumR1
  sumR2 = fmap SumR2
  prdR l r = PrdR <$> l <*> r
  stringR = pure . StringR

  covar v = Quoter (\ d -> Covar (toIndexed d v))
  µL b = MuL <$> binder (\ d' -> Quoter (\ d -> var (toIndexed d d'))) b
  lamL a b = LamL <$> a <*> b
  sumL l r = SumL <$> go l <*> go r where go = binder (\ d' -> Quoter (\ d -> var (toIndexed d d')))
  prdL1 b = PrdL1 <$> binder (\ d' -> Quoter (\ d -> var (toIndexed d d'))) b
  prdL2 b = PrdL2 <$> binder (\ d' -> Quoter (\ d -> var (toIndexed d d'))) b

  (.|.) = liftA2 (:|:)

var :: Index -> Term
var = Var . Free

covar :: Index -> Coterm
covar = Covar . Free


interpretTerm :: C.Sequent t c d => [t] -> [c] -> Term -> t
interpretTerm _G _D = \case
  Var (Free n)   -> _G `index` n
  Var (Global n) -> C.var (Global n)
  MuR b          -> C.µR (\ k -> interpretCommand _G (k:_D) b)
  LamR b         -> C.lamR (\ a k -> interpretCommand (a:_G) (k:_D) b)
  SumR1 t        -> C.sumR1 (interpretTerm _G _D t)
  SumR2 t        -> C.sumR2 (interpretTerm _G _D t)
  PrdR l r       -> C.prdR (interpretTerm _G _D l) (interpretTerm _G _D r)
  StringR s      -> C.stringR s

interpretCoterm :: C.Sequent t c d => [t] -> [c] -> Coterm -> c
interpretCoterm _G _D = \case
  Covar (Free n)   -> _D `index` n
  Covar (Global n) -> C.covar (Global n)
  MuL b            -> C.µL (\ t -> interpretCommand (t:_G) _D b)
  LamL a k         -> C.lamL (interpretTerm _G _D a) (interpretCoterm _G _D k)
  SumL l r         -> C.sumL (go l) (go r) where go d t =interpretCommand (t:_G) _D d
  PrdL1 c          -> C.prdL1 (\ t -> interpretCommand (t:_G) _D c)
  PrdL2 c          -> C.prdL2 (\ t -> interpretCommand (t:_G) _D c)

interpretCommand :: C.Sequent t c d => [t] -> [c] -> Command -> d
interpretCommand _G _D (t :|: c) = interpretTerm _G _D t C..|. interpretCoterm _G _D c

index :: [a] -> Index -> a
index as (Index i) = as !! i
