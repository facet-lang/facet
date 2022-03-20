{-# LANGUAGE FunctionalDependencies #-}
module Facet.Sequent.Class
( -- * Sequent abstraction
  Sequent(..)
  -- * Effectful abstractions
, varA
, µRA
, C.Clause(..)
, lamRA
, stringRA
, covarA
, µLA
, lamLA
, sumLA
, prdLA
, (.||.)
-- , Ctx(..)
-- , Binding(..)
-- , lookupCtx
) where

import Control.Applicative (liftA2)
import Data.Text (Text)
import Facet.Functor.Compose as C
import Facet.Name (Level, RName)
import Facet.Syntax (Var, type (~>))

-- * Term abstraction

class Sequent term coterm command | coterm -> term command, term -> coterm command, command -> term coterm where
  -- Terms
  var :: Var Level -> term
  µR :: (coterm -> command) -> term
  lamR :: (term -> coterm -> command) -> term
  sumR :: RName -> term -> term
  prdR :: [term] -> term
  stringR :: Text -> term

  -- Coterms
  covar :: Var Level -> coterm
  µL :: (term -> command) -> coterm
  lamL :: term -> coterm -> coterm
  sumL :: [term -> command] -> coterm
  prdL :: Int -> ([term] -> command) -> coterm

  -- Commands
  (.|.) :: term -> coterm -> command

  infix 1 .|.


-- * Effectful abstractions

varA :: (Sequent t c d, Applicative i, Applicative m) => Var Level -> m (i t)
varA v = pure (pure (var v))

µRA
  :: (Sequent t c d, Applicative i, Applicative m)
  => (forall j . Applicative j => (i ~> j) -> j c -> m (j d))
  -> m (i t)
µRA = binder µR

lamRA :: (Sequent t c d, Applicative i, Applicative m) => (forall j . Applicative j => (i ~> j) -> j t -> j c -> m (j d)) -> m (i t)
lamRA f = inner (\ wk v -> f wk (fst <$> v) (snd <$> v)) where
  inner = binder (lamR . curry)

stringRA :: (Sequent t c d, Applicative i, Applicative m) => Text -> m (i t)
stringRA = pure . pure . stringR


covarA :: (Sequent t c d, Applicative i, Applicative m) => Var Level -> m (i c)
covarA v = pure (pure (covar v))

µLA
  :: (Sequent t c d, Applicative i, Applicative m)
  => (forall j . Applicative j => (i ~> j) -> j t -> m (j d))
  -> m (i c)
µLA = binder µL

lamLA
  :: (Sequent t c d, Applicative i, Applicative m)
  => m (i t)
  -> m (i c)
  -> m (i c)
lamLA = liftA2 (liftA2 lamL)

sumLA
  :: (Sequent t c d, Applicative i, Applicative m)
  => [C.Clause m i t d]
  -> m (i c)
sumLA cs = runC (sumL <$> traverse (\ (C.Clause c) -> C (binder id c)) cs)

prdLA
  :: (Sequent t c d, Applicative i, Applicative m)
  => Int
  -> (forall j . Applicative j => (i ~> j) -> j [t] -> m (j d))
  -> m (i c)
prdLA i = binder (prdL i)


(.||.) :: (Applicative m, Applicative i, Sequent t c d) => m (i t) -> m (i c) -> m (i d)
(.||.) = liftA2 (liftA2 (.|.))

infix 1 .||.


-- data Ctx j t
--   = Nil
--   | forall i . Ctx i t :> Binding i j t

-- infixl 5 :>

-- data Binding i j t = Binding Name (i ~> j) (j t)

-- lookupCtx :: Name -> Ctx i t -> Maybe (i t)
-- lookupCtx n = go id
--   where
--   go :: (i ~> j) -> Ctx i t -> Maybe (j t)
--   go wk = \case
--     Nil                   -> Nothing
--     c :> Binding n' wk' t -> wk t <$ guard (n == n') <|> go (wk . wk') c
