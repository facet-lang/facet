{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FunctionalDependencies #-}
module Facet.Sequent.Class
( -- * Sequent abstraction
  Term(..)
, Coterm(..)
, Command(..)
, (.$.)
  -- * Effectful abstractions
, varA
, µRA
, lamRA
, (.$$.)
, stringRA
, covarA
, µLA
, lamLA
, sumLA
, prdL1A
, prdL2A
, (.||.)
, letA
, Ctx(..)
, Binding(..)
, lookupCtx
) where

import Control.Applicative (liftA2, (<|>))
import Control.Monad (guard)
import Data.Text (Text)
import Facet.Functor.Compose as C
import Facet.Name (Level, Name)
import Facet.Syntax (Var, type (~>))

-- * Term abstraction

class Term term coterm command | coterm -> term command, term -> coterm command, command -> term coterm where
  var :: Var Level -> term
  µR :: (coterm -> command) -> term
  lamR :: (term -> coterm -> command) -> term
  sumR :: Int -> term -> term
  bottomR :: command -> term
  unitR :: term
  prdR :: term -> term -> term
  stringR :: Text -> term

class Coterm term coterm command | coterm -> term command, term -> coterm command, command -> term coterm where
  covar :: Var Level -> coterm
  µL :: (term -> command) -> coterm
  lamL :: term -> coterm -> coterm
  sumL :: [coterm] -> coterm
  unitL :: coterm
  prdL1 :: coterm -> coterm
  prdL2 :: coterm -> coterm

class Command term coterm command | coterm -> term command, term -> coterm command, command -> term coterm where
  (.|.) :: term -> coterm -> command
  let' :: term -> (term -> command) -> command

  infix 1 .|.

(.$.) :: Coterm term coterm command => term -> coterm -> coterm
(.$.) = lamL

infixr 9 .$.


-- * Effectful abstractions

varA :: (Term t c d, Applicative i, Applicative m) => Var Level -> m (i t)
varA v = pure (pure (var v))

µRA
  :: (Term t c d, Applicative i, Applicative m)
  => (forall j . Applicative j => (i ~> j) -> j c -> m (j d))
  -> m (i t)
µRA = binder µR

lamRA :: (Term t c d, Applicative i, Applicative m) => (forall j . Applicative j => (i ~> j) -> j t -> j c -> m (j d)) -> m (i t)
lamRA f = inner (\ wk v -> f wk (fst <$> v) (snd <$> v)) where
  inner = binder (lamR . curry)

stringRA :: (Term t c d, Applicative i, Applicative m) => Text -> m (i t)
stringRA = pure . pure . stringR


covarA :: (Coterm t c d, Applicative i, Applicative m) => Var Level -> m (i c)
covarA v = pure (pure (covar v))

µLA
  :: (Coterm t c d, Applicative i, Applicative m)
  => (forall j . Applicative j => (i ~> j) -> j t -> m (j d))
  -> m (i c)
µLA = binder µL

lamLA
  :: (Coterm t c d, Applicative i, Applicative m)
  => m (i t)
  -> m (i c)
  -> m (i c)
lamLA = liftA2 (liftA2 lamL)

(.$$.)
  :: (Coterm t c d, Applicative i, Applicative m)
  => m (i t)
  -> m (i c)
  -> m (i c)
(.$$.) = lamLA

infixr 9 .$$.

sumLA
  :: (Coterm t c d, Applicative i, Applicative m)
  => m (i [c])
  -> m (i c)
sumLA = fmap (fmap sumL)

-- sumLA
--   :: (Coterm t c d, Applicative i, Applicative m)
--   => [C.Clause m i t d]
--   -> m (i c)
-- sumLA cs = runC (sumL <$> traverse (\ (C.Clause c) -> C (binder id c)) cs)

prdL1A
  :: (Coterm t c d, Applicative i, Applicative m)
  => m (i c)
  -> m (i c)
prdL1A = fmap (fmap prdL1)

prdL2A
  :: (Coterm t c d, Applicative i, Applicative m)
  => m (i c)
  -> m (i c)
prdL2A = fmap (fmap prdL2)


(.||.) :: (Applicative m, Applicative i, Command t c d) => m (i t) -> m (i c) -> m (i d)
(.||.) = liftA2 (liftA2 (.|.))

infix 1 .||.

letA :: (Applicative m, Applicative i, Command t c d) => m (i t) -> (forall j . Applicative j => (i ~> j) -> j t -> m (j d)) -> m (i d)
letA t b = liftA2 let' <$> t <*> (runC <$> b weaken (liftCInner id))


data Ctx j t
  = Nil
  | forall i . Ctx i t :> Binding i j t

infixl 5 :>

data Binding i j t = Binding Name (i ~> j) (j t)

lookupCtx :: Name -> Ctx i t -> Maybe (i t)
lookupCtx n = go id
  where
  go :: (i ~> j) -> Ctx i t -> Maybe (j t)
  go wk = \case
    Nil                   -> Nothing
    c :> Binding n' wk' t -> wk t <$ guard (n == n') <|> go (wk . wk') c
