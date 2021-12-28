{-# LANGUAGE ExistentialQuantification #-}
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
, (.||.)
, Ctx(..)
) where

import Control.Applicative (liftA2)
import Data.Text (Text)
import Facet.Functor.Compose
import Facet.Name (Level, Name, RName)
import Facet.Syntax (Var, type (~>))

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

funRA :: (Sequent t c d, Applicative i, Applicative m) => (forall j . Applicative j => (forall x . i x -> j x) -> j t -> m (j t))-> m (i t)
funRA f = fmap funR <$> binder f


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


(.||.) :: (Applicative m, Applicative i, Sequent t c d) => m (i t) -> m (i c) -> m (i d)
(.||.) = liftA2 (liftA2 (.|.))

infix 1 .||.


data Ctx j t
  = Nil
  | forall i . Entry Name (Ctx i t) (i ~> j) (j t)
