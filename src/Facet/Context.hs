module Facet.Context
( -- * Contexts
  Context(..)
, empty
, (|>)
, level
, (!?)
, (!)
, lookupLevel
) where

import           Facet.Name
import qualified Facet.Stack as S
import           Facet.Syntax
import           GHC.Stack
import           Prelude hiding (lookup)

newtype Context a = Context { elems :: S.Stack (Name ::: a) }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

empty :: Context a
empty = Context S.Nil

(|>) :: Context a -> Name ::: a -> Context a
Context as |> a = Context (as S.:> a)

infixl 5 |>

level :: Context a -> Level
level (Context c) = Level (length c)

(!?) :: Context a -> Index -> Maybe (Name ::: a)
c !? i = elems c S.!? getIndex i

(!) :: HasCallStack => Context a -> Index -> Name ::: a
c ! i = elems c S.! getIndex i

lookupLevel :: Name -> Context a -> Maybe (Level, a)
lookupLevel n c = go (Index 0) $ elems c
  where
  go _ S.Nil                = Nothing
  go i (cs S.:> (n' ::: a))
    | n == n'               = Just (indexToLevel (level c) i, a)
    | otherwise             = go (succ i) cs
