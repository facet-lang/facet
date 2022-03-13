{-# LANGUAGE ExistentialQuantification #-}
module Facet.Elab.Pattern
( Pattern(..)
, Clause(..)
, patterns_
, Type(..)
, Constructor(..)
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
import Control.Monad (ap, (<=<))
import Facet.Interface
import Facet.Name
import Fresnel.Effect hiding (view)
import Fresnel.Fold
import Fresnel.Lens
import Fresnel.List (head_)
import Fresnel.Traversal (traversed)

data Pattern a
  = Wildcard
  | Var a
  | Cons RName [Pattern a]
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
    Cons n p -> Cons n (map (>>= f) p)
    InL p    -> InL (p >>= f)
    InR q    -> InR (q >>= f)
    Pair p q -> Pair (p >>= f) (q >>= f)


data Clause a = Clause { patterns :: [Pattern Name], body :: a }

patterns_ :: Lens' (Clause a) [Pattern Name]
patterns_ = lens patterns (\ c patterns -> c{patterns})


data Type
  = String
  | ForAll
  | Arrow
  | One
  | Type :+ Type
  | Type :* Type
  | Comp (Signature Type)
  | Datatype RName [Constructor]
  deriving (Eq, Ord, Show)

data Constructor = Constructor
  { name   :: RName
  , fields :: [Type]
  }
  deriving (Eq, Ord, Show)

data Tableau = Tableau
  { context :: [Type]
  , heads   :: [Clause ()]
  }

heads_ :: Lens' Tableau [Clause ()]
heads_ = lens heads (\ t heads -> t{heads})

context_ :: Lens' Tableau [Type]
context_ = lens context (\ t context -> t{context})


data Branch s m a = forall x . Branch (Fold s x) (x -> m a)

(\/) :: Fold s a -> Fold s a -> Fold s a
f1 \/ f2 = getUnion (Union f1 <> Union f2)

infixr 2 \/


-- Coverage judgement

newtype Covers m a = Covers { runCovers :: StateC Tableau m a }
  deriving (Algebra (State Tableau :+: sig), Applicative, Functor, Monad, MonadFail)

instance Semigroup a => Semigroup (Covers m a) where
  a <> b = liftA2 (<>) a b

instance Monoid a => Monoid (Covers m a) where
  mempty = pure mempty


covers :: Tableau -> Either String Bool
covers t = run (runFail (runChoose (liftA2 (&&)) (const (pure True)) (execState t (runCovers go)))) where
  go = use context_ >>= \case
    [] -> pure ()
    _  -> coverStep >> go

coverStep :: (Has Choose sig m, MonadFail m) => Covers m ()
coverStep = use context_ >>= \case
  String:ctx   -> match ctx (\case
    Wildcard -> pure tail
    Var _    -> pure tail
    p        -> fail ("unexpected pattern: " <> show p))
  ForAll{}:ctx -> match ctx (\case
    Wildcard -> pure tail
    Var _    -> pure tail
    p        -> fail ("unexpected pattern: " <> show p))
  Arrow{}:ctx  -> match ctx (\case
    Wildcard -> pure tail
    Var _    -> pure tail
    p        -> fail ("unexpected pattern: " <> show p))
  One:ctx      -> match ctx (\case
    Wildcard  -> pure tail
    Var _     -> pure tail
    Cons _ [] -> pure tail
    p         -> fail ("unexpected pattern: " <> show p))
  (t1 :+ t2):ctx -> use heads_ >>= foldMapOf (folded.patterns_) (\case
      Wildcard:ps -> pure ([Clause (Wildcard:ps) ()], [Clause (Wildcard:ps) ()])
      Var n:ps    -> pure ([Clause (Var n:ps) ()],    [Clause (Var n:ps) ()])
      InL p:ps    -> pure ([Clause (p:ps) ()],        [Clause [] ()])
      InR q:qs    -> pure ([Clause [] ()],            [Clause (q:qs) ()])
      p:_         -> fail ("unexpected pattern: " <> show p)
      _           -> fail "no patterns to match sum")
    >>= \ (cs1, cs2) -> put (Tableau (t1:ctx) cs1) <|> put (Tableau (t2:ctx) cs2)
  (t1 :* t2):ctx -> match (t1:t2:ctx) (\case
    Wildcard   -> pure (\ clauses -> Wildcard:Wildcard:tail clauses)
    -- FIXME: substitute variables out for wildcards so we don't have to bind fresh variable names
    Var n      -> pure (\ clauses -> Var n:Var n:tail clauses)
    Pair p1 p2 -> pure (\ clauses -> p1:p2:tail clauses)
    p          -> fail ("unexpected pattern: " <> show p))
  Comp{}:ctx   -> match ctx (\ p -> fail ("unexpected pattern: " <> show p))
  Datatype _ []:ctx -> match ctx (\case
    Wildcard -> pure tail
    Var _    -> pure tail
    p        -> fail ("unexpected pattern: " <> show p))
  Datatype _ [Constructor m []]:ctx -> match ctx (\case
    Wildcard           -> pure tail
    Var _              -> pure tail
    Cons n [] | m == n -> pure tail
    p                  -> fail ("unexpected pattern: " <> show p))
  Datatype{}:ctx -> match ctx (\ p -> fail ("unexpected pattern: " <> show p))
  []           -> pure () -- FIXME: fail if clauses aren't all empty

match :: Algebra sig m => [Type] -> (Pattern Name -> Covers m ([Pattern Name] -> [Pattern Name])) -> Covers m ()
match ctx f = use heads_ >>= traverseOf_ (folded.patterns_.head_) ((\ g -> heads_.traversed.patterns_ %= g) <=< f) >> context_ .= ctx
