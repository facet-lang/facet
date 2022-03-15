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
, Covers(..)
, covers
, coverStep
) where

import Control.Applicative (Alternative(..), asum)
import Control.Monad (ap)
import Data.Bifunctor
import Data.Monoid
import Facet.Name
import Fresnel.Fold
import Fresnel.Lens
import Fresnel.Prism (Prism', matching, prism')
import Fresnel.Traversal (forOf, traversed)

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

context_ :: Lens' (Tableau a) [Type]
context_ = lens context (\ t context -> t{context})

heads_ :: Lens (Tableau a) (Tableau b) [Clause a] [Clause b]
heads_ = lens heads (\ t heads -> t{heads})


data Branch s m a = forall x . Branch (Fold s x) (x -> m a)

(\/) :: Fold s a -> Fold s a -> Fold s a
f1 \/ f2 = getUnion (Union f1 <> Union f2)

infixr 2 \/


-- Coverage judgement

newtype Covers e a = Covers { runCovers :: forall r . (r -> r -> r) -> (a -> r) -> r -> (e -> r) -> r }
  deriving (Functor)

instance Bifunctor Covers where
  bimap f g (Covers e) = Covers (\ fork leaf nil err -> e fork (leaf . g) nil (err . f))

instance Applicative (Covers e) where
  pure a = Covers (\ _ leaf _ _ -> leaf a)

  (<*>) = ap

instance Alternative (Covers e) where
  empty = Covers (\ _ _ nil _ -> nil)

  Covers a <|> Covers b = Covers (\ (<|>) leaf nil err -> a (<|>) leaf nil err <|> b (<|>) leaf nil err)

instance Monad (Covers e) where
  Covers m >>= k = Covers (\ fork leaf nil err -> m fork (\ a -> runCovers (k a) fork leaf nil err) nil err)

throw :: e -> Covers e a
throw e = Covers (\ _ _ _ err -> err e)

covers :: Tableau () -> Covers String (Tableau ())
covers tableau = case context tableau of
  [] -> pure tableau
  _  -> first (uncurry formatError) (coverStep tableau) >>= covers
  where
  formatError t = \case
    []  -> "expected " <> show t <> ", got nothing"
    p:_ -> "expected " <> show t <> ", got " <> show p

coverStep :: Tableau () -> Covers (Type, [Pattern Name]) (Tableau ())
coverStep tableau@(Tableau context heads) = case context of
  t:ctx -> case t of
    Opaque   -> Tableau ctx <$> forOf (traversed.patterns_) heads (\case
      Wildcard:ps -> pure ps
      Var _:ps    -> pure ps
      ps          -> throw (Opaque, ps))
    One      -> do
      canonical <- asum (map pure (wild t))
      Tableau ctx <$> forOf (traversed.patterns_) heads (\case
        p:ps | Right _ <- matching _Unit (instantiateHead canonical p) -> pure ps
        ps                                                             -> throw (t, ps))
    t1 :+ t2 -> getAp (foldMapOf (folded.patterns_) (Ap . \case
      Wildcard:ps -> pure ([Clause (Wildcard:ps) ()], [Clause (Wildcard:ps) ()])
      Var n:ps    -> pure ([Clause (Var n:ps) ()],    [Clause (Var n:ps) ()])
      InL p:ps    -> pure ([Clause (p:ps) ()],        [Clause [] ()])
      InR q:qs    -> pure ([Clause [] ()],            [Clause (q:qs) ()])
      ps          -> throw (t1 :+ t2, ps)) heads)
      >>= \ (cs1, cs2) -> pure (Tableau (t1:ctx) cs1) <|> pure (Tableau (t2:ctx) cs2)
    t1 :* t2 -> Tableau (t1:t2:ctx) <$> forOf (traversed.patterns_) heads (\case
      Wildcard:ps   -> pure (Wildcard:Wildcard:ps)
      -- FIXME: substitute variables out for wildcards so we don't have to bind fresh variable names
      Var n:ps      -> pure (Var n:Var n:ps)
      Pair p1 p2:ps -> pure (p1:p2:ps)
      ps            -> throw (t1 :* t2, ps))
  []           -> pure tableau -- FIXME: fail if clauses aren't all empty

instantiateHead :: Pattern Name -> Pattern Name -> Pattern Name
instantiateHead d Wildcard = d
instantiateHead d (Var _)  = d -- FIXME: let-bind any variables first
instantiateHead _ p        = p


wild :: Type -> [Pattern Name]
wild = \case
  Opaque -> [Wildcard]
  One    -> [Unit]
  _ :+ _ -> [InL Wildcard, InR Wildcard]
  _ :* _ -> [Pair Wildcard Wildcard]
