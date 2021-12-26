{-# LANGUAGE FunctionalDependencies #-}
module Facet.Sequent.Class
( -- * Sequent abstraction
  Sequent(..)
  -- * Effectful abstractions
, µRA
, Clause(..)
, funRA
, µLA
, sumLA
, prdLA
) where

import Data.Text (Text)
import Facet.Functor.Compose
import Facet.Name (Level, RName)
import Facet.Syntax (Var)

-- * Term abstraction

class Sequent term coterm command | coterm -> term command, term -> coterm command, command -> term coterm where
  -- Terms
  var :: Var Level -> term
  µR :: (coterm -> command) -> term
  funR :: (term -> term) -> term
  sumR :: RName -> term -> term
  prdR :: [term] -> term
  stringR :: Text -> term

  -- Coterms
  covar :: Var Level -> coterm
  µL :: (term -> command) -> coterm
  funL :: term -> coterm -> coterm
  sumL :: [term -> command] -> coterm
  prdL :: Int -> ([term] -> command) -> coterm

  -- Commands
  (.|.) :: term -> coterm -> command

  infix 1 .|.


-- * Effectful abstractions

µRA
  :: (Sequent t c d, Applicative i, Applicative m)
  => (forall j . Applicative j => (forall x . i x -> j x) -> j c -> m (j d))
  -> m (i t)
µRA f = fmap µR <$> binder f

funRA :: (Sequent t c d, Applicative i, Applicative m) => Clause m i t t -> m (i t)
funRA (Clause c) = runC (funR <$> C (binder c))


µLA
  :: (Sequent t c d, Applicative i, Applicative m)
  => (forall j . Applicative j => (forall x . i x -> j x) -> j t -> m (j d))
  -> m (i c)
µLA f = fmap µL <$> binder f

sumLA
  :: (Sequent t c d, Applicative i, Applicative m)
  => [Clause m i t d]
  -> m (i c)
sumLA cs = runC (sumL <$> traverse (\ (Clause c) -> C (binder c)) cs)

prdLA
  :: (Sequent t c d, Applicative i, Applicative m)
  => Int
  -> (forall j . Applicative j => (forall x . i x -> j x) -> j [t] -> m (j d))
  -> m (i c)
prdLA i f = fmap (prdL i) <$> binder f
