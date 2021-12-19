{-# LANGUAGE FunctionalDependencies #-}
module Facet.Sequent.Class
( -- * Sequent abstraction
  Sequent(..)
  -- * Effectful abstractions
, strengthen
, µRA
, Clause(..)
, funRA
, µLA
, sumLA
) where

import Control.Applicative (liftA2)
import Data.Functor.Identity (Identity(..))
import Data.Text (Text)
import Facet.Functor.Compose
import Facet.Name (LName, Level, Name, RName)
import Facet.Pattern (Pattern)
import Facet.Syntax (Var, (:=:)(..))

-- * Term abstraction

class Sequent term coterm command | coterm -> term command, term -> coterm command, command -> term coterm where
  -- Terms
  var :: Var (LName Level) -> term
  µR :: (coterm -> command) -> term
  funR :: [(Pattern Name, Pattern (Name :=: term) -> term)] -> term
  sumR1 :: term -> term
  sumR2 :: term -> term
  conR :: RName -> [term] -> term
  stringR :: Text -> term
  dictR :: [RName :=: term] -> term
  compR :: [RName :=: Name] -> (Pattern (Name :=: term) -> term) -> term

  -- Coterms
  covar :: Var (LName Level) -> coterm
  µL :: (term -> command) -> coterm
  funL :: term -> coterm -> coterm
  sumL :: (term -> command) -> (term -> command) -> coterm

  -- Commands
  (.|.) :: term -> coterm -> command

  infix 1 .|.


-- * Effectful abstractions

strengthen :: Applicative m => m (Identity a) -> m a
strengthen = fmap runIdentity


µRA
  :: (Sequent t c d, Applicative i, Applicative m)
  => (forall j . Applicative j => (forall x . i x -> j x) -> j c -> m (j d))
  -> m (i t)
µRA f = fmap µR <$> binder f

newtype Clause m i t c d a = Clause { runClause :: forall j . Applicative j => (forall x . i x -> j x) -> j a -> m (j t) }

funRA :: (Sequent t c d, Applicative i, Applicative m) => [(Pattern Name, Clause m i t c d (Pattern (Name :=: t)))] -> m (i t)
funRA cs = runC (funR <$> traverse (traverse (\ (Clause c) -> C (binder c))) cs)


µLA
  :: (Sequent t c d, Applicative i, Applicative m)
  => (forall j . Applicative j => (forall x . i x -> j x) -> j t -> m (j d))
  -> m (i c)
µLA f = fmap µL <$> binder f

sumLA
  :: (Sequent t c d, Applicative i, Applicative m)
  => (forall j . Applicative j => (forall x . i x -> j x) -> j t -> m (j d))
  -> (forall j . Applicative j => (forall x . i x -> j x) -> j t -> m (j d))
  -> m (i c)
sumLA f g = liftA2 sumL <$> binder f <*> binder g
