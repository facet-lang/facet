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
, coverLoop
, coverStep
) where

import Control.Applicative (Alternative(..), liftA2)
import Control.Monad (ap)
import Data.Bifunctor
import Facet.Name
import Fresnel.Fold
import Fresnel.Lens
import Fresnel.Prism (Prism', matching', prism')
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

_InL :: Prism' (Pattern a) (Pattern a)
_InL = prism' InL (\case
  InL p -> Just p
  _     -> Nothing)

_InR :: Prism' (Pattern a) (Pattern a)
_InR = prism' InR (\case
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

instance Semigroup a => Semigroup (Covers e a) where
  (<>) = liftA2 (<>)

instance Monoid a => Monoid (Covers e a) where
  mempty = pure mempty

throw :: e -> Covers e a
throw e = Covers (\ _ _ _ err -> err e)

covers :: Tableau () -> Bool
covers t = runCovers (coverLoop t) (&&) (const True) True (const False)

coverLoop :: Tableau () -> Covers String (Tableau ())
coverLoop tableau = case context tableau of
  [] -> pure tableau
  _  -> first (uncurry formatError) (coverStep tableau) >>= coverLoop
  where
  formatError t = \case
    []  -> "expected " <> show t <> ", got nothing"
    p:_ -> "expected " <> show t <> ", got " <> show p

coverStep :: Tableau () -> Covers (Type, [Pattern Name]) (Tableau ())
coverStep tableau@(Tableau [] _) = pure tableau -- FIXME: fail if clauses aren't all empty
coverStep tableau@(Tableau (t:_) _) = case t of
  Opaque -> match (([] <$) . matching' _Wildcard) tableau
  One    -> match (([] <$) . matching' _Unit) tableau
  _ :+ _ -> match (\ p -> pure <$> (matching' _InL p <|> matching' _InR p)) tableau
  _ :* _ -> match (fmap (\ (a, b) -> [a, b]) . matching' _Pair) tableau

match :: (Pattern Name -> Maybe [Pattern Name]) -> Tableau a -> Covers (Type, [Pattern Name]) (Tableau a)
match _ tableau@(Tableau [] _)  = pure tableau
match decompose (Tableau (t:ctx) heads) = do
  (prefix, canonical) <- wild t
  Tableau (prefix <> ctx) <$> forOf (traversed.patterns_) heads (\case
    p:ps | Just p' <- decompose (instantiateHead canonical p) -> pure (p' <> ps)
    ps                                                        -> throw (t, ps))


instantiateHead :: Pattern Name -> Pattern Name -> Pattern Name
instantiateHead d Wildcard = d
instantiateHead d (Var _)  = d -- FIXME: let-bind any variables first
instantiateHead _ p        = p


wild :: Type -> Covers e ([Type], Pattern Name)
wild = \case
  Opaque -> pure ([], Wildcard)
  One    -> pure ([], Unit)
  s :+ t -> pure ([s], InL Wildcard) <|> pure ([t], InR Wildcard)
  s :* t -> pure ([s, t], Pair Wildcard Wildcard)
