{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Context
( Context(..)
, empty
, (|>)
, level
, (!?)
, (!)
) where

import           Facet.Name
import qualified Facet.Stack as S
import           Facet.Syntax
import           GHC.Stack

newtype Context a = Context { elems :: S.Stack (UName ::: a) }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

empty :: Context a
empty = Context S.Nil

(|>) :: Context a -> UName ::: a -> Context a
Context as |> a = Context (as S.:> a)

infixl 5 |>

level :: Context a -> Level
level (Context c) = Level (length c)

(!?) :: Context a -> Index -> Maybe (UName ::: a)
c !? i = elems c S.!? getIndex i

(!) :: HasCallStack => Context a -> Index -> UName ::: a
c ! i = elems c S.! getIndex i
