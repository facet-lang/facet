module Facet.Context
( -- * Contexts
  Context(..)
, empty
, (|>)
, level
, (!?)
, (!)
, lookupLevel
, Suffix
, (<><)
) where

import           Facet.Name
import qualified Facet.Stack as S
import           Facet.Syntax
import           GHC.Stack
import           Prelude hiding (lookup)

newtype Context a = Context { elems :: S.Stack (Name :=: Maybe a ::: a) }
  deriving (Eq, Ord, Show)

empty :: Context a
empty = Context S.Nil

(|>) :: Context a -> Name :=: Maybe a ::: a -> Context a
Context as |> a = Context (as S.:> a)

infixl 5 |>

level :: Context a -> Level
level (Context c) = Level (length c)

(!?) :: Context a -> Index -> Maybe (Name :=: Maybe a ::: a)
c !? i = elems c S.!? getIndex i

(!) :: HasCallStack => Context a -> Index -> Name :=: Maybe a ::: a
c ! i = elems c S.! getIndex i

lookupLevel :: Name -> Context a -> Maybe (Level, Maybe a ::: a)
lookupLevel n c = go (Index 0) $ elems c
  where
  go _ S.Nil                = Nothing
  go i (cs S.:> (n' :=: a))
    | n == n'               = Just (indexToLevel (level c) i, a)
    | otherwise             = go (succ i) cs


type Suffix a = [Name :=: a ::: a]

(<><) :: Context a -> Suffix a -> Context a
gamma <>< []                   = gamma
gamma <>< ((n :=: v ::: _T):s) = gamma |> (n :=: Just v ::: _T) <>< s

infixl 5 <><
