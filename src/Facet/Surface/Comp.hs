{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Surface.Comp
( Clause(..)
, clause_
, body_
) where

import Control.Lens (Prism', prism')
import Facet.Name
import Facet.Surface.Pattern (Pattern)
import Text.Parser.Position (Span, Spanned(..))

data Clause e
  = Clause (Pattern UName) (Clause e)
  | Body e
  | Loc Span (Clause e)
  deriving (Foldable, Functor, Show, Traversable)

instance Spanned (Clause e) where
  setSpan = Loc

  dropSpan = \case
    Loc _ d -> dropSpan d
    d       -> d


clause_ :: Prism' (Clause e) (Pattern UName, Clause e)
clause_ = prism' (uncurry Clause) (\case{ Clause n b -> Just (n, b) ; _ -> Nothing })

body_ :: Prism' (Clause e) e
body_ = prism' Body (\case{ Body e -> Just e ; _ -> Nothing })
