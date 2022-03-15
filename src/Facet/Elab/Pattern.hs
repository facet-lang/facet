{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Elab.Pattern
( Pattern(..)
, Clause(..)
, patterns_
, Type(..)
, Tableau(..)
, context_
, heads_
, Branch(..)
, (\/)
  -- * Coverage judgement
, covers
, coverStep
) where

import Control.Monad (ap, join)
import Data.Monoid
import Facet.Name
import Fresnel.Fold
import Fresnel.Lens
import Fresnel.Prism (Prism', prism')
import Fresnel.Traversal (traverseOf, traversed)

data Pattern a
  = Wildcard
  | Var a
  | Unit
  | InL (Pattern a)
  | InR (Pattern a)
  | Pair (Pattern a) (Pattern a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative Pattern where
  pure = Var
  (<*>) = ap

instance Monad Pattern where
  m >>= f = case m of
    Wildcard -> Wildcard
    Var a    -> f a
    Unit     -> Unit
    InL p    -> InL (p >>= f)
    InR q    -> InR (q >>= f)
    Pair p q -> Pair (p >>= f) (q >>= f)


_Wildcard :: Prism' (Pattern a) ()
_Wildcard = prism' (const Wildcard) (\case
  Wildcard -> Just ()
  _        -> Nothing)

_Var :: Prism' (Pattern a) a
_Var = prism' Var (\case
  Var a -> Just a
  _     -> Nothing)

_Unit :: Prism' (Pattern a) ()
_Unit = prism' (const Unit) (\case
  Unit -> Just ()
  _    -> Nothing)

_Inl :: Prism' (Pattern a) (Pattern a)
_Inl = prism' InL (\case
  InL p -> Just p
  _     -> Nothing)

_Inr :: Prism' (Pattern a) (Pattern a)
_Inr = prism' InR (\case
  InR p -> Just p
  _     -> Nothing)

_Pair :: Prism' (Pattern a) (Pattern a, Pattern a)
_Pair = prism' (uncurry Pair) (\case
  Pair p q -> Just (p, q)
  _        -> Nothing)


data Clause a = Clause { patterns :: [Pattern Name], body :: a }

patterns_ :: Lens' (Clause a) [Pattern Name]
patterns_ = lens patterns (\ c patterns -> c{patterns})


data Type
  = Opaque
  | One
  | Type :+ Type
  | Type :* Type
  deriving (Eq, Ord, Show)

infixl 6 :+
infixl 7 :*

data Tableau a = Tableau
  { context :: [Type]
  , heads   :: [Clause a]
  }

heads_ :: Lens (Tableau a) (Tableau b) [Clause a] [Clause b]
heads_ = lens heads (\ t heads -> t{heads})

context_ :: Lens' (Tableau a) [Type]
context_ = lens context (\ t context -> t{context})


data Branch s m a = forall x . Branch (Fold s x) (x -> m a)

(\/) :: Fold s a -> Fold s a -> Fold s a
f1 \/ f2 = getUnion (Union f1 <> Union f2)

infixr 2 \/


-- Coverage judgement

covers :: Tableau () -> Either String [Tableau ()]
covers tableau = case context tableau of
  [] -> Right [tableau]
  _  -> coverStep tableau >>= fmap join . traverse covers

coverStep :: Tableau () -> Either String [Tableau ()]
coverStep tableau@(Tableau context heads) = case context of
  Opaque:ctx   -> pure . Tableau ctx <$> match heads (\case
    Wildcard:ps -> Right ps
    Var _:ps    -> Right ps
    p           -> Left ("unexpected pattern: " <> show p))
  One:ctx      -> pure . Tableau ctx <$> match heads (\case
    Wildcard:ps -> Right ps
    Var _:ps    -> Right ps
    Unit:ps     -> Right ps
    p           -> Left ("unexpected pattern: " <> show p))
  t1 :+ t2:ctx -> getAp (foldMapOf (folded.patterns_) (Ap . \case
    Wildcard:ps -> Right ([Clause (Wildcard:ps) ()], [Clause (Wildcard:ps) ()])
    Var n:ps    -> Right ([Clause (Var n:ps) ()],    [Clause (Var n:ps) ()])
    InL p:ps    -> Right ([Clause (p:ps) ()],        [Clause [] ()])
    InR q:qs    -> Right ([Clause [] ()],            [Clause (q:qs) ()])
    p:_         -> Left ("unexpected pattern: " <> show p)
    _           -> Left "no patterns to match sum") heads)
    >>= \ (cs1, cs2) -> Right [Tableau (t1:ctx) cs1, Tableau (t2:ctx) cs2]
  t1 :* t2:ctx -> pure . Tableau (t1:t2:ctx) <$> match heads (\case
    Wildcard:ps   -> Right (Wildcard:Wildcard:ps)
    -- FIXME: substitute variables out for wildcards so we don't have to bind fresh variable names
    Var n:ps      -> Right (Var n:Var n:ps)
    Pair p1 p2:ps -> Right (p1:p2:ps)
    p             -> Left ("unexpected pattern: " <> show p))
  []           -> Right [tableau] -- FIXME: fail if clauses aren't all empty

match :: [Clause a] -> ([Pattern Name] -> Either String [Pattern Name]) -> Either String [Clause a]
match heads f = traverseOf (traversed.patterns_) f heads
