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
import Text.Parser.Position (Span, Spanned(..))

newtype Pattern a = In { out :: PatternF a (Pattern a) }

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
