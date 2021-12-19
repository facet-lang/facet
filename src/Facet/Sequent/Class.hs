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
µRA f = fmap µR . runC <$> f liftCOuter (liftCInner id)

newtype Clause i m t c d = Clause { runClause :: forall j . Applicative j => (forall x . i x -> j x) -> j (Pattern (Name :=: t)) -> m (j t) }

funRA :: (Sequent t c d, Applicative i, Applicative m) => [(Pattern Name, Clause i m t c d)] -> m (i t)
funRA cs = runC (funR <$> traverse (traverse (C . clause)) cs)
  where
  clause :: (Functor m, Applicative i) => Clause i m t c d -> m (i (Pattern (Name :=: t) -> t))
  clause (Clause c) = runC <$> c liftCOuter (liftCInner id)


µLA
  :: (Sequent t c d, Applicative i, Applicative m)
  => (forall j . Applicative j => (forall x . i x -> j x) -> j t -> m (j d))
  -> m (i c)
µLA f = fmap µL . runC <$> f liftCOuter (liftCInner id)

sumLA
  :: (Sequent t c d, Applicative i, Applicative m)
  => (forall j . Applicative j => j t -> m (j d))
  -> (forall j . Applicative j => j t -> m (j d))
  -> m (i c)
sumLA f g = (\ a b -> liftA2 sumL (runC a) (runC b)) <$> f (liftCInner id) <*> g (liftCInner id)
