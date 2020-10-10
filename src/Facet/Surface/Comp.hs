{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Surface.Comp
( Clause(..)
, mapComp
, clause_
, body_
) where

import Control.Lens (Prism', prism')
import Facet.Name
import Facet.Surface.Pattern (Pattern)
import Text.Parser.Position (Span, Spanned(..))

data Clause f a
  = Clause (Pattern UName) (Clause f a)
  | Body (f a)
  | Loc Span (Clause f a)
  deriving (Foldable, Functor, Show, Traversable)

instance Spanned (Clause f Span) where
  setSpan = Loc

  dropSpan = \case
    Loc _ d -> dropSpan d
    d       -> d


mapComp :: (f a -> g b) -> Clause f a -> Clause g b
mapComp f = go
  where
  go = \case
    Clause p c -> Clause p (go c)
    Body e     -> Body (f e)
    Loc s c    -> Loc s (go c)


clause_ :: Prism' (Clause f a) (Pattern UName, Clause f a)
clause_ = prism' (uncurry Clause) (\case{ Clause n b -> Just (n, b) ; _ -> Nothing })

body_ :: Prism' (Clause f a) (f a)
body_ = prism' Body (\case{ Body e -> Just e ; _ -> Nothing })
