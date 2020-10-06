{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Surface.Comp
( Comp(..)
, cases_
, expr_
, CompF(..)
, fold
) where

import Control.Category ((>>>))
import Control.Lens.Prism
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Facet.Name
import Text.Parser.Position (Span, Spanned(..))

newtype Comp e = In { out :: CompF e (Comp e) }

instance Foldable Comp where
  foldMap f = go where go = bifoldMap f go . out

instance Functor Comp where
  fmap f = go where go = In . bimap f go . out

instance Traversable Comp where
  traverse f = go where go = fmap In . bitraverse f go . out


cases_ :: Prism' (Comp e) [([Name], e)]
cases_ = prism' (In . Cases) (\case{ In (Cases cs) -> Just cs ; _ -> Nothing })

expr_ :: Prism' (Comp e) e
expr_ = prism' (In . Expr) (\case{ In (Expr e) -> Just e ; _ -> Nothing })


data CompF e c
  = Cases [([Name], e)]
  | Expr e
  | Loc Span c
  deriving (Foldable, Functor, Traversable)

instance Bifoldable CompF where
  bifoldMap = bifoldMapDefault

instance Bifunctor CompF where
  bimap = bimapDefault

  second = fmap

instance Bitraversable CompF where
  bitraverse f g = \case
    Cases cs -> Cases <$> traverse (traverse f) cs
    Expr e   -> Expr <$> f e
    Loc s c  -> Loc s <$> g c

instance Spanned (Comp e) where
  setSpan = fmap In . Loc

  dropSpan = out >>> \case
    Loc _ d -> dropSpan d
    d       -> In d


fold :: (CompF e a -> a) -> Comp e -> a
fold alg = go
  where
  go = alg . fmap go . out
