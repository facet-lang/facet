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
import Control.Carrier.State.Church
import Control.Effect.Choose
import Control.Monad (ap)
import Facet.Interface
import Facet.Name
import Fresnel.Effect hiding (view)
import Fresnel.Fold
import Fresnel.Getter
import Fresnel.Lens
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
    Unit     -> Unit
    Var a    -> f a
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
  | Comp (Signature Type)
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

newtype Covers m a = Covers { runCovers :: StateC (Tableau ()) m a }
  deriving (Algebra (State (Tableau ()) :+: sig), Applicative, Functor, Monad, MonadFail)

instance Semigroup a => Semigroup (Covers m a) where
  a <> b = liftA2 (<>) a b

instance Monoid a => Monoid (Covers m a) where
  mempty = pure mempty


covers :: Tableau () -> Either String Bool
covers t = run (runFail (runChoose (liftA2 (&&)) (const (pure True)) (execState t (runCovers go)))) where
  go = use (context_ @()) >>= \case
    [] -> pure ()
    _  -> coverStep >> go

coverStep :: (Has Choose sig m, MonadFail m) => Covers m ()
coverStep = use (context_ @()) >>= \case
  Opaque:ctx   -> match ctx (\case
    Wildcard:ps -> pure ps
    Var _:ps    -> pure ps
    p           -> fail ("unexpected pattern: " <> show p))
  One:ctx      -> match ctx (\case
    Wildcard:ps -> pure ps
    Var _:ps    -> pure ps
    Unit:ps     -> pure ps
    p           -> fail ("unexpected pattern: " <> show p))
  t1 :+ t2:ctx -> use (heads_ @()) >>= foldMapOf (folded.patterns_) (\case
      Wildcard:ps -> pure ([Clause (Wildcard:ps) ()], [Clause (Wildcard:ps) ()])
      Var n:ps    -> pure ([Clause (Var n:ps) ()],    [Clause (Var n:ps) ()])
      InL p:ps    -> pure ([Clause (p:ps) ()],        [Clause [] ()])
      InR q:qs    -> pure ([Clause [] ()],            [Clause (q:qs) ()])
      p:_         -> fail ("unexpected pattern: " <> show p)
      _           -> fail "no patterns to match sum")
    >>= \ (cs1, cs2) -> put (Tableau (t1:ctx) cs1) <|> put (Tableau (t2:ctx) cs2)
  t1 :* t2:ctx -> match (t1:t2:ctx) (\case
    Wildcard:ps   -> pure (Wildcard:Wildcard:ps)
    -- FIXME: substitute variables out for wildcards so we don't have to bind fresh variable names
    Var n:ps      -> pure (Var n:Var n:ps)
    Pair p1 p2:ps -> pure (p1:p2:ps)
    p             -> fail ("unexpected pattern: " <> show p))
  Comp{}:ctx   -> match ctx (\ p -> fail ("unexpected pattern: " <> show p))
  []           -> pure () -- FIXME: fail if clauses aren't all empty

match :: Algebra sig m => [Type] -> ([Pattern Name] -> Covers m [Pattern Name]) -> Covers m ()
match ctx f = heads_ @() <~> traverseOf (traversed.patterns_) f >> context_ @() .= ctx

-- | Compose a getter onto the input of a Kleisli arrow and run it on the 'State'.
(~>) :: Has (State s) sig m => Getter s a -> (a -> m b) -> m b
o ~> k = use o >>= k

infixr 2 ~>

-- | Compose a lens onto either side of a Kleisli arrow and run it on the 'State'.
(<~>) :: Has (State s) sig m => Lens' s a -> (a -> m a) -> m ()
o <~> k = o <~ o ~> k

infixr 2 <~>
