module Facet.Sequent.Pattern
( -- * Patterns
  Pattern(..)
, _Wildcard
, _Var
, _Unit
, _InL
, _InR
, _Pair
  -- * Copatterns
, Copattern(..)
, _All
, _Op
) where

import Control.Monad (ap)
import Fresnel.Prism (Prism', prism')

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


data Copattern a
  = All (Maybe a)
  | Op (Pattern a) (Maybe a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)


_All :: Prism' (Copattern a) (Maybe a)
_All = prism' All (\case
  All v -> Just v
  Op{}  -> Nothing)

_Op :: Prism' (Copattern a) (Pattern a, Maybe a)
_Op = prism' (uncurry Op) (\case
  Op p k -> Just (p, k)
  All{}  -> Nothing)
