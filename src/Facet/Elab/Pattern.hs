{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Elab.Pattern
( Pattern(..)
, Clause(..)
, patterns_
, Type(..)
, Tableau(..)
, heads_
, Branch(..)
, (\/)
  -- * Coverage judgement
, Covers(..)
, covers
, coverStep
) where

import Control.Algebra
import Control.Applicative (liftA2)
import Control.Carrier.Choose.Church (ChooseC, runChoose)
import Control.Carrier.Fail.Either
import Control.Effect.Choose
import Control.Monad (ap)
import Control.Monad.Trans.Class
import Data.Function
import Facet.Name
import Fresnel.Fold
import Fresnel.Lens
import Fresnel.Prism (Prism', prism')
import Fresnel.Setter
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

runCovers :: (FailC m r -> FailC m r -> FailC m r) -> (a -> FailC m r) -> Covers m a -> m (Either String r)
runCovers fork leaf (Covers m) = runFail (runChoose fork leaf m)

newtype Covers m a = Covers (ChooseC (FailC m) a)
  deriving (Algebra (Choose :+: Fail :+: sig), Applicative, Functor, Monad)

instance Algebra sig m => MonadFail (Covers m) where
  fail = Covers . lift . fail

instance (Applicative m, Semigroup a) => Semigroup (Covers m a) where
  (<>) = liftA2 (<>)

instance (Applicative m, Monoid a) => Monoid (Covers m a) where
  mempty = pure mempty


covers :: Tableau () -> Either String Bool
covers t = run (runCovers (liftA2 (&&)) (const (pure True)) (go t)) where
  go tableau = case context tableau of
    [] -> pure ()
    _  -> coverStep tableau >>= go

coverStep :: Algebra sig m => Tableau () -> Covers m (Tableau ())
coverStep tableau = case context tableau of
  Opaque:ctx   -> match (tableau & context_ .~ ctx) (\case
    Wildcard:ps -> pure ps
    Var _:ps    -> pure ps
    p           -> fail ("unexpected pattern: " <> show p))
  One:ctx      -> match (tableau & context_ .~ ctx) (\case
    Wildcard:ps -> pure ps
    Var _:ps    -> pure ps
    Unit:ps     -> pure ps
    p           -> fail ("unexpected pattern: " <> show p))
  t1 :+ t2:ctx -> foldMapOf (folded.patterns_) (\case
      Wildcard:ps -> pure ([Clause (Wildcard:ps) ()], [Clause (Wildcard:ps) ()])
      Var n:ps    -> pure ([Clause (Var n:ps) ()],    [Clause (Var n:ps) ()])
      InL p:ps    -> pure ([Clause (p:ps) ()],        [Clause [] ()])
      InR q:qs    -> pure ([Clause [] ()],            [Clause (q:qs) ()])
      p:_         -> fail ("unexpected pattern: " <> show p)
      _           -> fail "no patterns to match sum") (heads tableau)
    >>= \ (cs1, cs2) -> pure (Tableau (t1:ctx) cs1) <|> pure (Tableau (t2:ctx) cs2)
  t1 :* t2:ctx -> match (tableau & context_ .~ t1:t2:ctx) (\case
    Wildcard:ps   -> pure (Wildcard:Wildcard:ps)
    -- FIXME: substitute variables out for wildcards so we don't have to bind fresh variable names
    Var n:ps      -> pure (Var n:Var n:ps)
    Pair p1 p2:ps -> pure (p1:p2:ps)
    p             -> fail ("unexpected pattern: " <> show p))
  []           -> pure tableau -- FIXME: fail if clauses aren't all empty

match :: Tableau () -> ([Pattern Name] -> Covers m [Pattern Name]) -> Covers m (Tableau ())
match tableau f = flip (set (heads_ @())) tableau <$> traverseOf (traversed.patterns_) f (heads tableau)
