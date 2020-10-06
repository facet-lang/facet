{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Surface.Pattern
( Pattern(..)
, wildcard_
, var_
, tuple_
, PatternF(..)
) where

import Control.Category ((>>>))
import Control.Lens (Prism', prism')
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Text.Parser.Position (Span, Spanned(..))

newtype Pattern a = In { out :: PatternF a (Pattern a) }

instance Foldable Pattern where
  foldMap f = go where go = bifoldMap f go . out

instance Functor Pattern where
  fmap f = go where go = In . bimap f go . out

instance Traversable Pattern where
  traverse f = go where go = fmap In . bitraverse f go . out

instance Spanned (Pattern a) where
  setSpan = fmap In . Loc

  dropSpan = out >>> \case
    Loc _ d -> dropSpan d
    d       -> In d


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
  | Loc Span p
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
    Loc s p  -> Loc s <$> g p
