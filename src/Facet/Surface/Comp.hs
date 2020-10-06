{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Surface.Comp
( Clause(..)
, clause_
, body_
, ClauseF(..)
, fold
) where

import Control.Category ((>>>))
import Control.Lens (Prism', prism')
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Facet.Name
import Facet.Surface.Pattern (Pattern)
import Text.Parser.Position (Span, Spanned(..))

newtype Clause e = In { out :: ClauseF e (Clause e) }

instance Foldable Clause where
  foldMap f = go where go = bifoldMap f go . out

instance Functor Clause where
  fmap f = go where go = In . bimap f go . out

instance Traversable Clause where
  traverse f = go where go = fmap In . bitraverse f go . out

instance Spanned (Clause e) where
  setSpan = fmap In . Loc

  dropSpan = out >>> \case
    Loc _ d -> dropSpan d
    d       -> In d


clause_ :: Prism' (Clause e) (Pattern Name, Clause e)
clause_ = prism' (In . uncurry Clause) (\case{ In (Clause n b) -> Just (n, b) ; _ -> Nothing })

body_ :: Prism' (Clause e) e
body_ = prism' (In . Body) (\case{ In (Body e) -> Just e ; _ -> Nothing })


data ClauseF e c
  = Clause (Pattern Name) c
  | Body e
  | Loc Span c
  deriving (Foldable, Functor, Traversable)

instance Bifoldable ClauseF where
  bifoldMap = bifoldMapDefault

instance Bifunctor ClauseF where
  bimap = bimapDefault

  second = fmap

instance Bitraversable ClauseF where
  bitraverse f g = \case
    Clause n c -> Clause n <$> g c
    Body e     -> Body <$> f e
    Loc s c    -> Loc s <$> g c


fold :: (ClauseF e a -> a) -> Clause e -> a
fold alg = go
  where
  go = alg . fmap go . out
