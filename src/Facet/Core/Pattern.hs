{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Core.Pattern
( Pattern(..)
, wildcard_
, var_
, tuple_
) where

import Control.Lens (Prism', prism')
import Facet.Vars

data Pattern a
  = Wildcard
  | Var a
  | Tuple [Pattern a]
  deriving (Foldable, Functor, Show, Traversable)

instance Scoped a => Scoped (Pattern a) where
  fvs = \case
    Wildcard -> mempty
    Var n    -> fvs n
    Tuple ps -> foldMap fvs ps


wildcard_ :: Prism' (Pattern a) ()
wildcard_ = prism' (const Wildcard) (\case{ Wildcard -> Just () ; _ -> Nothing })

var_ :: Prism' (Pattern a) a
var_ = prism' Var (\case{ Var a -> Just a ; _ -> Nothing })

tuple_ :: Prism' (Pattern a) [Pattern a]
tuple_ = prism' Tuple (\case{ Tuple ps -> Just ps ; _ -> Nothing })
