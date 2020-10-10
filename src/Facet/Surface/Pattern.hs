{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Surface.Pattern
( Pattern(..)
, wildcard_
, var_
, tuple_
) where

import Control.Lens (Prism', prism')
import Text.Parser.Position (Span, Spanned(..))

data Pattern a
  = Wildcard
  | Var a
  | Tuple [Pattern a]
  | Loc Span (Pattern a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Spanned (Pattern a) where
  setSpan = Loc
  dropSpan = \case
    Loc _ p -> p
    p       -> p


wildcard_ :: Prism' (Pattern a) ()
wildcard_ = prism' (const Wildcard) (\case{ Wildcard -> Just () ; _ -> Nothing })

var_ :: Prism' (Pattern a) a
var_ = prism' Var (\case{ Var a -> Just a ; _ -> Nothing })

tuple_ :: Prism' (Pattern a) [Pattern a]
tuple_ = prism' Tuple (\case{ Tuple ps -> Just ps ; _ -> Nothing })
