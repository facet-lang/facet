module Facet.Snoc.NonEmpty
( NonEmpty(..)
, (|>)
) where

import Facet.Snoc

data NonEmpty a = Snoc a :|> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixl 5 :|>

(|>) :: NonEmpty a -> a -> NonEmpty a
i :|> l |> l' = i :> l :|> l'

infixl 5 |>
