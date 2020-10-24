module Facet.Context
( -- * Contexts
  Context(..)
, empty
, (|>)
, level
, names
, (!?)
, (!)
, lookupLevel
) where

import           Facet.Name
import qualified Facet.Stack as S
import           Facet.Syntax
import           GHC.Stack
import           Prelude hiding (lookup)

newtype Context a = Context { elems :: S.Stack (UName ::: a) }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

empty :: Context a
empty = Context S.Nil

(|>) :: Context a -> UName ::: a -> Context a
Context as |> a = Context (as S.:> a)

infixl 5 |>

level :: Context a -> Level
level (Context c) = Level (length c)

names :: Context a -> S.Stack UName
names = fmap tm . elems

(!?) :: Context a -> Index -> Maybe (UName ::: a)
c !? i = elems c S.!? getIndex i

(!) :: HasCallStack => Context a -> Index -> UName ::: a
c ! i = elems c S.! getIndex i

lookupLevel :: UName -> Context a -> Maybe (Level, a)
lookupLevel n c = go (Index 0) $ elems c
  where
  go _ S.Nil                = Nothing
  go i (cs S.:> (n' ::: a))
    | n == n'               = Just (indexToLevel (level c) i, a)
    | otherwise             = go (succ i) cs
