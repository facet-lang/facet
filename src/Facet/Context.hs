{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Context
( Context(..)
, empty
, (|>)
, level
, (!?)
, (|-)
, lookupBound
) where

import           Control.Carrier.Reader
import           Facet.Name
import qualified Facet.Stack as S
import           Facet.Syntax

newtype Context a = Context { getContext :: S.Stack (UName ::: a) }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

empty :: Context a
empty = Context S.Nil

(|>) :: Context a -> UName ::: a -> Context a
Context as |> a = Context (as S.:> a)

infixl 5 |>

level :: Context a -> Level
level (Context c) = Level (length c)

(!?) :: Context a -> Index -> Maybe (UName ::: a)
c !? i = getContext c S.!? getIndex i


(|-) :: Has (Reader (Context a)) sig m => UName ::: a -> m b -> m b
t |- m = local (Context . (S.:> t) . getContext) m

infix 1 |-

lookupBound :: Has (Reader (Context a)) sig m => Index -> m (Maybe (UName ::: a))
lookupBound = asks . flip (!?)
