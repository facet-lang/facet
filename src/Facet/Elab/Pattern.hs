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
import Control.Carrier.Writer.Church (execWriter)
import Control.Effect.Choose
import Control.Monad (ap)
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


covers :: Tableau -> Either String Bool
covers t = run (runFail (runChoose (liftA2 (&&)) (const (pure True)) (execState t (runCovers go)))) where
  go = use context_ >>= \case
    [] -> pure ()
    _  -> coverStep >> go

coverStep :: (Has Choose sig m, MonadFail m) => Covers m ()
coverStep = use context_ >>= \case
  String:ctx   -> match (\case
    Wildcard -> pure ()
    Var _    -> pure ()
    p        -> fail ("unexpected pattern: " <> show p)) >> context_ .= ctx >> heads_.traversed.patterns_ %= tail
  ForAll{}:ctx -> match (\case
    Wildcard -> pure ()
    Var _    -> pure ()
    p        -> fail ("unexpected pattern: " <> show p)) >> context_ .= ctx >> heads_.traversed.patterns_ %= tail
  Arrow{}:ctx  -> match (\case
    Wildcard -> pure ()
    Var _    -> pure ()
    p        -> fail ("unexpected pattern: " <> show p)) >> context_ .= ctx >> heads_.traversed.patterns_ %= tail
  One:ctx      -> match (\case
    Wildcard  -> pure ()
    Var _     -> pure ()
    Cons _ [] -> pure ()
    p         -> fail ("unexpected pattern: " <> show p)) >> context_ .= ctx >> heads_.traversed.patterns_ %= tail
  (t1 :+ t2):ctx -> use heads_ >>= execWriter . traverseOf_ (folded.patterns_) (\case
      Wildcard:ps -> pure ([Clause (Wildcard:ps)], [Clause (Wildcard:ps)])
      Var n:ps    -> pure ([Clause (Var n:ps)],    [Clause (Var n:ps)])
      InL p:ps    -> pure ([Clause (p:ps)],        [Clause []])
      InR q:qs    -> pure ([Clause []],            [Clause (q:qs)])
      p:_         -> fail ("unexpected pattern: " <> show p)
      _           -> fail "no patterns to match sum")
    >>= \ (cs1, cs2) -> put (Tableau (t1:ctx) cs1) <|> put (Tableau (t2:ctx) cs2)
  (t1 :* t2):ctx -> match (\case
    Wildcard   -> context_ .= t1:t2:ctx >> heads_.traversed.patterns_ %= (\ clause -> Wildcard:Wildcard:clause)
    -- FIXME: this should bind fresh names
    Var n      -> context_ .= t1:t2:ctx >> heads_.traversed.patterns_ %= (\ clause -> Var n:Var n:clause)
    Pair p1 p2 -> context_ .= t1:t2:ctx >> heads_.traversed.patterns_ %= (\ clause -> p1:p2:clause)
    p          -> fail ("unexpected pattern: " <> show p))
  Comp{}:_     -> match (\ p -> fail ("unexpected pattern: " <> show p))
  Datatype _ []:ctx -> match (\case
    Wildcard -> pure ()
    Var _    -> pure ()
    p        -> fail ("unexpected pattern: " <> show p)) >> context_ .= ctx >> heads_.traversed.patterns_ %= tail
  Datatype _ [Constructor m []]:ctx -> match (\case
    Wildcard           -> pure ()
    Var _              -> pure ()
    Cons n [] | m == n -> pure ()
    p                  -> fail ("unexpected pattern: " <> show p)) >> context_ .= ctx >> heads_.traversed.patterns_ %= tail
  Datatype{}:_ -> match (\ p -> fail ("unexpected pattern: " <> show p))
  []           -> pure () -- FIXME: fail if clauses aren't all empty

match :: Algebra sig m => (Pattern Name -> Covers m ()) -> Covers m ()
match f = use heads_ >>= traverseOf_ (folded.patterns_.head_) f
