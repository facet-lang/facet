{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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
, lookupCtx
  -- * Temp
, covers
, Branch(..)
, Tm(..)
, Ty(..)
, Pat(..)
) where

import Control.Applicative (Alternative(..), liftA2)
import Control.Monad (ap, guard, (<=<))
import Data.Bifunctor (Bifunctor(..))
import Data.Functor.Contravariant
import Data.Text (Text)
import Data.These
import Facet.Functor.Compose
import Facet.Name (Level, Name, RName)
import Facet.Syntax (Var, type (~>))
import Fresnel.Getter ((^.))
import Fresnel.Lens
import Fresnel.Setter
import Fresnel.Traversal (traverseOf)

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

{-

binary sums indicate constructor solely by position, i.e. inl : left command :: inr : right command. how would they represent wildcard or variable patterns?

e.g.

{ (some (false)) -> A
, _              -> B }

~~>

µ̃[ɩₗ(x). cₗ | ɩᵣ(x). cᵣ]

1. unpack choices into separate branches

µ̃[ɩₗ(x). … | ɩᵣ(x). …]

2. unpack contents of branches recursively


G |-



µ̃[ɩₗ(x). cₗ | ɩᵣ(x). cᵣ]

-}

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

lookupCtx :: Name -> Ctx i t -> Maybe (i t)
lookupCtx n = go id
  where
  go :: (i ~> j) -> Ctx i t -> Maybe (j t)
  go wk = \case
    Nil              -> Nothing
    Entry n' c wk' t -> wk t <$ guard (n == n') <|> go (wk . wk') c


data Tm
  = Unit
  | InL Tm
  | InR Tm
  | Case String Tm String Tm
  | Pair Tm Tm
  | PrjL String Tm
  | PrjR String Tm
  | Let String Tm Tm
  | Lam String Tm
  | App Tm Tm

data Ty
  = Zero
  | One
  | Ty :+ Ty
  | Ty :* Ty
  | Ty :-> Ty

infixl 6 :+
infixl 7 :*
infixl 0 :->

data Pat
  = PWildcard
  | PVar String
  | POne
  | PPair Pat Pat
  | PInL Pat
  | PInR Pat
  deriving (Eq, Ord, Show)

-- _PVar :: Prism' Pat String
-- _PVar = prism' PVar (\case
--   PVar a -> Just a
--   _      -> Nothing)


type PList = [Pat]

data Branch = Branch
  { patterns :: PList
  , body     :: Tm
  }

patterns_ :: Lens Branch Branch [Pat] [Pat]
patterns_ = lens patterns (\ (Branch _ e) ps -> Branch ps e)

type Clauses = [Branch]
type Context = [Ty]

covers :: Context -> Clauses -> Bool
covers ctx bs
  | [] <- ctx = True
  | otherwise = maybe False (all (uncurry covers)) (covers1 ctx bs)

covers1 :: Context -> Clauses -> Maybe [(Context, Clauses)]
covers1 ctx bs = case ctx of
  [] -> Just [([], bs)]
  t:ts -> case t of
    Zero    -> runDecompose (reset decomposeZero) (Just . pure . (ts,)) bs
    One     -> runDecompose (reset decomposeOne) (Just . pure . (ts,)) bs
    s :+ t  -> runDecompose (reset decomposeSum) (Just . uncurry (<>) . bimap (pure . (s:ts,)) (pure . (t:ts,))) bs
    s :* t  -> runDecompose (reset decomposeProduct) (Just . pure . (s:t:ts,)) bs
    _ :-> _ -> runDecompose (reset decomposeExp) (Just . pure . (ts,)) bs

reset :: Decompose r r -> Decompose r' r
reset (Decompose m) = Decompose (\ k c -> m Just c >>= k)

decomposeZero :: Decompose Clauses Clauses
decomposeZero = decomposePatterns $ \case
  PWildcard:ps -> Just ps
  PVar _:ps    -> Just ps
  _            -> Nothing

decomposeOne :: Decompose Clauses Clauses
decomposeOne = decomposePatterns $ \case
  POne:ps      -> Just ps
  PWildcard:ps -> Just ps
  PVar _:ps    -> Just ps
  _            -> Nothing

decomposeSum :: Decompose (Clauses, Clauses) (Clauses, Clauses)
decomposeSum = Decompose $ \ k -> k <=< fmap partitionHereThere . traverse (\ b -> bimap (flip (set patterns_) b) (flip (set patterns_) b) <$> go (b^.patterns_)) where
  go = \case
    PInL p:ps    -> Just (This (p:ps))
    PInR q:ps    -> Just (That (q:ps))
    PWildcard:ps -> Just (These (PWildcard:ps) (PWildcard:ps))
    PVar v:ps    -> Just (These (PVar v:ps) (PVar v:ps))
    _            -> Nothing

decomposeProduct :: Decompose Clauses Clauses
decomposeProduct = decomposePatterns $ \case
  PPair p q:ps -> Just (p:q:ps)
  PWildcard:ps -> Just (PWildcard:PWildcard:ps)
  PVar v:ps    -> Just (PVar v:PVar v:ps)
  _            -> Nothing

decomposeExp :: Decompose Clauses Clauses
decomposeExp = decomposePatterns $ \case
  PWildcard:ps -> Just ps
  PVar _:ps    -> Just ps
  _            -> Nothing

newtype Decompose r a = Decompose { runDecompose :: (a -> Maybe r) -> (Clauses -> Maybe r) }
  deriving (Functor)

instance Applicative (Decompose r) where
  pure a = Decompose (\ k _ -> k a)
  (<*>) = ap

instance Monad (Decompose r) where
  Decompose m >>= f = Decompose (\ k c -> m (\ a -> runDecompose (f a) k c) c)

-- newtype Cover = Cover _

decomposePatterns :: ([Pat] -> Maybe [Pat]) -> Decompose Clauses Clauses
decomposePatterns go = Decompose (\ f -> f <=< traverse (traverseOf patterns_ go))


newtype Match a b = Match { match :: b -> Maybe a }

instance Contravariant (Match a) where
  contramap f (Match g) = Match (g . f)

prd :: Match c a -> Match c b -> Match c (a, b)
prd ma mb = Match (\ (a, b) -> match ma a *> match mb b)
