{-# LANGUAGE ExistentialQuantification #-}
module Facet.Elab.Pattern
( Atom(..)
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
import Control.Carrier.Writer.Church (execWriter)
import Control.Effect.Choose
import Control.Monad (ap)
import Facet.Interface
import Facet.Name
import Fresnel.Effect hiding (view)
import Fresnel.Fold
import Fresnel.Iso
import Fresnel.Lens
import Fresnel.List (head_)
import Fresnel.Traversal (traversed)

data Atom a
  = Wildcard
  | Var a
  | Unit
  | InL (Atom a)
  | InR (Atom a)
  | Pair (Atom a) (Atom a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative Atom where
  pure = Var
  (<*>) = ap

instance Monad Atom where
  m >>= f = case m of
    Wildcard -> Wildcard
    Var a    -> f a
    Unit     -> Unit
    InL p    -> InL (p >>= f)
    InR q    -> InR (q >>= f)
    Pair p q -> Pair (p >>= f) (q >>= f)


newtype Clause = Clause [Atom Name]

patterns_ :: Iso' Clause [Atom Name]
patterns_ = coerced


data Type
  = String
  | ForAll
  | Arrow
  | Zero
  | One
  | Type :+ Type
  | Type :* Type
  | Comp (Signature Type)


data Tableau = Tableau
  { context :: [Type]
  , heads   :: [Clause]
  }

heads_ :: Lens' Tableau [Clause]
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
  String:ctx   -> use heads_ >>= traverseOf_ (folded.patterns_.head_) (\case
    Wildcard -> pure ()
    Var _    -> pure ()
    p        -> fail ("unexpected pattern: " <> show p)) >> context_ .= ctx >> heads_.traversed.patterns_ %= tail
  ForAll{}:ctx -> use heads_ >>= traverseOf_ (folded.patterns_.head_) (\case
    Wildcard -> pure ()
    Var _    -> pure ()
    p        -> fail ("unexpected pattern: " <> show p)) >> context_ .= ctx >> heads_.traversed.patterns_ %= tail
  Arrow{}:ctx  -> use heads_ >>= traverseOf_ (folded.patterns_.head_) (\case
    Wildcard -> pure ()
    Var _    -> pure ()
    p        -> fail ("unexpected pattern: " <> show p)) >> context_ .= ctx >> heads_.traversed.patterns_ %= tail
  Zero:ctx     -> use heads_ >>= traverseOf_ (folded.patterns_.head_) (\case
    Wildcard -> pure ()
    Var _    -> pure ()
    p        -> fail ("unexpected pattern: " <> show p)) >> context_ .= ctx >> heads_.traversed.patterns_ %= tail
  One:ctx      -> use heads_ >>= traverseOf_ (folded.patterns_.head_) (\case
    Wildcard -> pure ()
    Var _    -> pure ()
    Unit     -> pure ()
    p        -> fail ("unexpected pattern: " <> show p)) >> context_ .= ctx >> heads_.traversed.patterns_ %= tail
  (t1 :+ t2):ctx -> use heads_ >>= execWriter . traverseOf_ (folded.patterns_) (\case
      Wildcard:ps -> pure ([Clause (Wildcard:ps)], [Clause (Wildcard:ps)])
      Var n:ps    -> pure ([Clause (Var n:ps)],    [Clause (Var n:ps)])
      InL p:ps    -> pure ([Clause (p:ps)],        [Clause []])
      InR q:qs    -> pure ([Clause []],            [Clause (q:qs)])
      p:_         -> fail ("unexpected pattern: " <> show p)
      _           -> fail "no patterns to match sum")
    >>= \ (cs1, cs2) -> put (Tableau (t1:ctx) cs1) <|> put (Tableau (t2:ctx) cs2)
  (t1 :* t2):ctx -> use heads_ >>= traverseOf_ (folded.patterns_.head_) (\case
    Wildcard   -> context_ .= t1:t2:ctx >> heads_.traversed.patterns_ %= (\ clause -> Wildcard:Wildcard:clause)
    -- FIXME: this should bind fresh names
    Var n      -> context_ .= t1:t2:ctx >> heads_.traversed.patterns_ %= (\ clause -> Var n:Var n:clause)
    Pair p1 p2 -> context_ .= t1:t2:ctx >> heads_.traversed.patterns_ %= (\ clause -> p1:p2:clause)
    p          -> fail ("unexpected pattern: " <> show p))
  Comp{}:_     -> use heads_ >>= traverseOf_ (folded.patterns_.head_) (\ p -> fail ("unexpected pattern: " <> show p))
  []           -> pure () -- FIXME: fail if clauses aren't all empty
