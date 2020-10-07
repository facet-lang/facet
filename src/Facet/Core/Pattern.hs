{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Core.Pattern
( Pattern(..)
, wildcard_
, var_
, tuple_
, PatternF(..)
, fold
) where

import Control.Category ((>>>))
import Control.Lens (Prism', prism')
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Facet.Vars

newtype Pattern a = In { out :: PatternF a (Pattern a) }
  deriving newtype (Show)

instance Foldable Pattern where
  foldMap f = go where go = bifoldMap f go . out

instance Functor Pattern where
  fmap f = go where go = In . bimap f go . out

instance Traversable Pattern where
  traverse f = go where go = fmap In . bitraverse f go . out

instance Scoped a => Scoped (Pattern a) where
  fvs = out >>> \case
    Wildcard -> mempty
    Var n    -> fvs n
    Tuple ps -> foldMap fvs ps


wildcard_ :: Prism' (Pattern a) ()
wildcard_ = prism' (const (In Wildcard)) (\case{ In Wildcard -> Just () ; _ -> Nothing })

var_ :: Prism' (Pattern a) a
var_ = prism' (In . Var) (\case{ In (Var a) -> Just a ; _ -> Nothing })

tuple_ :: Prism' (Pattern a) [Pattern a]
tuple_ = prism' (In . Tuple) (\case{ In (Tuple ps) -> Just ps ; _ -> Nothing })


data PatternF a p
  = Wildcard
  | Var a
  | Tuple [p]
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bifoldable PatternF where
  bifoldMap = bifoldMapDefault

instance Bifunctor PatternF where
  bimap = bimapDefault

  second = fmap

instance Bitraversable PatternF where
  bitraverse f g = \case
    Wildcard -> pure Wildcard
    Var a    -> Var <$> f a
    Tuple ps -> Tuple <$> traverse g ps


fold :: (PatternF n a -> a) -> Pattern n -> a
fold alg = go
  where
  go = alg . fmap go . out
