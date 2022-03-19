{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Elab.Pattern
( Pattern(..)
, Clause(..)
, patterns_
, Type(..)
, Branch(..)
, (\/)
  -- * Coverage judgement
, Covers(..)
, covers
, coverLoop
, coverStep
) where

import Control.Applicative (Alternative(..), asum)
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
  | Type :-> Type
  deriving (Eq, Ord, Show)

infixl 6 :+
infixl 7 :*
infixl 1 :->


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

covers :: Type -> [Clause a] -> Bool
covers ty heads = runCovers (coverLoop ty heads) (&&) (const True) True (const False)

coverLoop :: Type -> [Clause a] -> Covers String (Type, [Clause a])
coverLoop ty heads = case ty of
  hd :-> tl -> first (uncurry formatError) (coverStep hd heads) >>= \ (prefix, hd) -> coverLoop (prefix tl) hd
  ty        -> pure (ty, heads) -- FIXME: fail if clauses aren't all empty
  where
  formatError t = \case
    []  -> "expected " <> show t <> ", got nothing"
    p:_ -> "expected " <> show t <> ", got " <> show p

coverStep :: Type -> [Clause a] -> Covers (Type, [Pattern Name]) (Type -> Type, [Clause a])
coverStep hd heads = case hd of
  Opaque  -> match [([], Wildcard)]                           hd heads (\ p -> [] <$ matching' _Wildcard p)
  One     -> match [([], Unit)]                               hd heads (\ p -> [] <$ matching' _Unit p)
  s :+ t  -> match [([s], InL Wildcard), ([t], InR Wildcard)] hd heads (\ p -> pure <$> (matching' _InL p <|> matching' _InR p)) -- FIXME: match once and partition results
  s :* t  -> match [([s, t], Pair Wildcard Wildcard)]         hd heads (\ p -> (\ (a, b) -> [a, b]) <$> matching' _Pair p)
  _ :-> _ -> match [([], Wildcard)]                           hd heads (\ p -> [] <$ matching' _Wildcard p)

match :: [([Type], Pattern Name)] -> Type -> [Clause a] -> (Pattern Name -> Maybe [Pattern Name]) -> Covers (Type, [Pattern Name]) (Type -> Type, [Clause a])
match inst hd heads decompose = do
  (prefix, canonical) <- asum (pure <$> inst)
  (\ tl -> foldr (:->) tl prefix,) <$> forOf (traversed.patterns_) heads (\case
    p:ps | Just p' <- decompose (instantiateHead canonical p) -> pure (p' <> ps)
    ps                                                        -> throw (hd, ps))


instantiateHead :: Pattern Name -> Pattern Name -> Pattern Name
instantiateHead d Wildcard = d
instantiateHead d (Var _)  = d -- FIXME: let-bind any variables first
instantiateHead _ p        = p
