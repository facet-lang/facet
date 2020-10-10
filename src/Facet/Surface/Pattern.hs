{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Surface.Pattern
( Pattern(..)
, wildcard_
, var_
, tuple_
, PatternF(..)
) where

import Control.Lens (Prism', prism')
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Text.Parser.Position (Span)

data Pattern a = In { ann :: Span, out :: PatternF a (Pattern a) }

instance Show a => Show (Pattern a) where
  showsPrec p = showsPrec p . out

instance Foldable Pattern where
  foldMap f = go where go = bifoldMap f go . out

instance Functor Pattern where
  fmap f = go where go = In . ann <*> bimap f go . out

instance Traversable Pattern where
  traverse f = go where go = fmap . In . ann <*> bitraverse f go . out


wildcard_ :: Prism' (Pattern a) Span
wildcard_ = prism' (`In` Wildcard) (\case{ In s Wildcard -> Just s ; _ -> Nothing })

var_ :: Prism' (Pattern a) (Span, a)
var_ = prism' (uncurry In . fmap Var) (\case{ In s (Var a) -> Just (s, a) ; _ -> Nothing })

tuple_ :: Prism' (Pattern a) (Span, [Pattern a])
tuple_ = prism' (uncurry In . fmap Tuple) (\case{ In s (Tuple ps) -> Just (s, ps) ; _ -> Nothing })


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
