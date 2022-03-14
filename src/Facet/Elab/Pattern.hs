{-# LANGUAGE ExistentialQuantification #-}
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
import Control.Carrier.Choose.Church (runChoose)
import Control.Carrier.Fail.Either
import Control.Effect.Choose
import Control.Monad (ap)
import Data.Function
import Facet.Name
import Fresnel.Fold
import Fresnel.Lens
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

newtype Covers m a = Covers { runCovers :: m a }
  deriving (Algebra sig, Applicative, Functor, Monad, MonadFail)

instance (Applicative m, Semigroup a) => Semigroup (Covers m a) where
  a <> b = liftA2 (<>) a b

instance (Applicative m, Monoid a) => Monoid (Covers m a) where
  mempty = pure mempty


covers :: Tableau () -> Either String Bool
covers t = run (runFail (runChoose (liftA2 (&&)) (const (pure True)) (runCovers (go t)))) where
  go tableau = case context tableau of
    [] -> pure ()
    _  -> coverStep tableau >>= go

coverStep :: (Has Choose sig m, MonadFail m) => Tableau () -> Covers m (Tableau ())
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

match :: Algebra sig m => Tableau () -> ([Pattern Name] -> Covers m [Pattern Name]) -> Covers m (Tableau ())
match tableau f = flip (set (heads_ @())) tableau <$> traverseOf (traversed.patterns_) f (heads tableau)
