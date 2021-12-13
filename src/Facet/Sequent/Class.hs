{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Sequent.Class
( -- * Sequent abstraction
  Sequent(..)
  -- * Effectful abstractions
, strengthen
, µRA
, Clause(..)
, funRA
, µLA
  -- * Commands
, (:|:)(..)
) where

import Control.Applicative (liftA2)
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Functor.Identity (Identity(..))
import Data.Text (Text)
import Facet.Functor.Compose
import Facet.Name (LName, Level, Name, RName)
import Facet.Pattern (Pattern)
import Facet.Quote (Quote(..))
import Facet.Syntax (Var, (:=:)(..))

-- * Term abstraction

class Sequent term coterm command | coterm -> term command, term -> coterm command, command -> term coterm where
  -- Terms
  var :: Var (LName Level) -> term
  µR :: Name -> (coterm -> command) -> term
  funR :: [(Pattern Name, Pattern (Name :=: term) -> term)] -> term
  conR :: RName -> [term] -> term
  stringR :: Text -> term
  dictR :: [RName :=: term] -> term
  compR :: [RName :=: Name] -> (Pattern (Name :=: term) -> term) -> term

  -- Coterms
  covar :: Var (LName Level) -> coterm
  µL :: Name -> (term -> command) -> coterm
  funL :: term -> coterm -> coterm

  -- Commands
  (.|.) :: term -> coterm -> command

  infix 1 .|.


-- * Effectful abstractions

strengthen :: Applicative m => m (Identity a) -> m a
strengthen = fmap runIdentity


µRA
  :: (Sequent t c d, Applicative i, Applicative m)
  => Name
  -> (forall j . Applicative j => (forall x . i x -> j x) -> j c -> m (j d))
  -> m (i t)
µRA n f = fmap (µR n) . runC <$> f liftCOuter (liftCInner id)

newtype Clause i m t = Clause { runClause :: forall j . Applicative j => (forall x . i x -> j x) -> j (Pattern (Name :=: t)) -> m (j t) }

funRA :: (Sequent t c d, Applicative i, Applicative m) => [(Pattern Name, Clause i m t)] -> m (i t)
funRA cs = fmap funR <$> runC (traverse (traverse (\ c -> C (runC <$> runClause c liftCOuter (liftCInner id)))) cs)


µLA
  :: (Sequent t c d, Applicative i, Applicative m)
  => Name
  -> (forall j . Applicative j => (forall x . i x -> j x) -> j t -> m (j d))
  -> m (i c)
µLA n f = fmap (µL n) . runC <$> f liftCOuter (liftCInner id)


-- * Commands

data term :|: coterm = term :|: coterm

instance (Quote term1 term2, Quote coterm1 coterm2) => Quote (term1 :|: coterm1) (term2 :|: coterm2) where
  quote (term :|: coterm) = liftA2 (:|:) (quote term) (quote coterm)

instance Bifoldable (:|:) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (:|:) where
  bimap = bimapDefault

instance Bitraversable (:|:) where
  bitraverse f g (a :|: b) = (:|:) <$> f a <*> g b
