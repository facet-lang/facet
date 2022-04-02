module Facet.Sequent.Expr
( -- * Terms
  Term(..)
  -- * Coterms
, Coterm(..)
  -- * Commands
, Command(..)
  -- ** Smart constructors
, varA
, µRA
, lamRA
, lamRA'
, covarA
, µLA
, sumLA
, prdL1A
, prdL2A
, (.||.)
, letA
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
  | UnitR
  | PrdR Term Term
  | StringR Text


-- Coterms

data Coterm
  = Covar (Var Index)
  | MuL Command
  | LamL Term Coterm
  | SumL Coterm Coterm
  | UnitL
  | PrdL1 Coterm
  | PrdL2 Coterm


-- Commands

data Command
  = Term :|: Coterm
  | Let Term Command


instance C.Sequent (Quoter Term) (Quoter Coterm) (Quoter Command) where
  var v = Quoter (\ d -> Var (toIndexed d v))
  µR b = MuR <$> binder (\ d' -> Quoter (\ d -> covar (toIndexed d d'))) b
  lamR b = LamR <$> binder (\ d' -> Quoter (\ d -> var (toIndexed d d'))) (binder (\ d'' -> Quoter (\ d -> covar (toIndexed d d''))) . b)
  sumR1 = fmap SumR1
  sumR2 = fmap SumR2
  unitR = pure UnitR
  prdR = liftA2 PrdR
  stringR = pure . StringR

  covar v = Quoter (\ d -> Covar (toIndexed d v))
  µL b = MuL <$> binder (\ d' -> Quoter (\ d -> var (toIndexed d d'))) b
  lamL = liftA2 LamL
  sumL = liftA2 SumL
  unitL = pure UnitL
  prdL1 = fmap PrdL1
  prdL2 = fmap PrdL2

  (.|.) = liftA2 (:|:)
  let' t b = Let <$> t <*> binder (\ d' -> Quoter (\ d -> var (toIndexed d d'))) b

var :: Index -> Term
var = Var . Free

covar :: Index -> Coterm
covar = Covar . Free


-- Smart constructors

varA :: Applicative m => Var Index -> m Term
varA = pure . Var

µRA :: Functor m => m Command -> m Term
µRA = fmap MuR

lamRA :: Functor m => m Command -> m Term
lamRA = fmap LamR

lamRA' :: Applicative m => (QuoterT m Term -> QuoterT m Coterm -> QuoterT m Command) -> QuoterT m Term
lamRA' body = LamR <$> body (QuoterT (\ level -> pure (var (toIndexed (succ level) level)))) (QuoterT (\ level -> pure (covar (toIndexed (succ level) (succ level)))))


covarA :: Applicative m => Var Index -> m Coterm
covarA = pure . Covar

µLA :: Functor m => m Command -> m Coterm
µLA = fmap MuL

sumLA
  :: Applicative m
  => m Coterm
  -> m Coterm
  -> m Coterm
sumLA = liftA2 SumL

prdL1A
  :: Applicative m
  => m Coterm
  -> m Coterm
prdL1A = fmap PrdL1

prdL2A
  :: Applicative m
  => m Coterm
  -> m Coterm
prdL2A = fmap PrdL2


(.||.) :: Applicative m => m Term -> m Coterm -> m Command
(.||.) = liftA2 (:|:)

infix 1 .||.

letA :: Applicative m => m Term -> m Command -> m Command
letA = liftA2 Let


-- Interpreters

interpretTerm :: C.Sequent t c d => [t] -> [c] -> Term -> t
interpretTerm _G _D = \case
  Var (Free n)   -> _G `index` n
  Var (Global n) -> C.var (Global n)
  MuR b          -> C.µR (\ k -> interpretCommand _G (k:_D) b)
  LamR b         -> C.lamR (\ a k -> interpretCommand (a:_G) (k:_D) b)
  SumR1 t        -> C.sumR1 (interpretTerm _G _D t)
  SumR2 t        -> C.sumR2 (interpretTerm _G _D t)
  UnitR          -> C.unitR
  PrdR l r       -> C.prdR (interpretTerm _G _D l) (interpretTerm _G _D r)
  StringR s      -> C.stringR s

interpretCoterm :: C.Sequent t c d => [t] -> [c] -> Coterm -> c
interpretCoterm _G _D = \case
  Covar (Free n)   -> _D `index` n
  Covar (Global n) -> C.covar (Global n)
  MuL b            -> C.µL (\ t -> interpretCommand (t:_G) _D b)
  LamL a k         -> C.lamL (interpretTerm _G _D a) (interpretCoterm _G _D k)
  SumL l r         -> C.sumL (interpretCoterm _G _D l) (interpretCoterm _G _D r)
  UnitL            -> C.unitL
  PrdL1 c          -> C.prdL1 (interpretCoterm _G _D c)
  PrdL2 c          -> C.prdL2 (interpretCoterm _G _D c)

interpretCommand :: C.Sequent t c d => [t] -> [c] -> Command -> d
interpretCommand _G _D (t :|: c) = interpretTerm _G _D t C..|. interpretCoterm _G _D c
interpretCommand _G _D (Let t b) = C.let' (interpretTerm _G _D t) (\ t -> interpretCommand (t:_G) _D b)

index :: [a] -> Index -> a
index as (Index i) = as !! i
