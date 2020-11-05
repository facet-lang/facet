module Facet.Context
( -- * Contexts
  Context(..)
, Entry
, Solution(..)
, empty
, (|>)
, level
, (!?)
, (!)
, lookupLevel
, Suffix
, (<><)
) where

import           Data.Foldable (foldl')
import           Facet.Name
import qualified Facet.Stack as S
import           Facet.Syntax
import           GHC.Stack
import           Prelude hiding (lookup)

newtype Context a = Context { elems :: S.Stack (Entry a) }
  deriving (Eq, Ord, Show)

type Entry a = Name :=: Solution a ::: a

data Solution a
  = Flex (Maybe a)
  | Rigid
  deriving (Eq, Ord, Show)

empty :: Context a
empty = Context S.Nil

(|>) :: Context a -> Entry a -> Context a
Context as |> a = Context (as S.:> a)

infixl 5 |>

level :: Context a -> Level
level (Context c) = Level (length c)

(!?) :: Context a -> Index -> Maybe (Entry a)
c !? i = elems c S.!? getIndex i

(!) :: HasCallStack => Context a -> Index -> Entry a
c ! i = elems c S.! getIndex i

lookupLevel :: Name -> Context a -> Maybe (Level, Solution a ::: a)
lookupLevel n c = go (Index 0) $ elems c
  where
  go _ S.Nil                = Nothing
  go i (cs S.:> (n' :=: a))
    | n == n'               = Just (indexToLevel (level c) i, a)
    | otherwise             = go (succ i) cs


type Suffix a = [Name :=: Maybe a ::: a]

(<><) :: Context a -> Suffix a -> Context a
(<><) = foldl' (\ gamma (n :=: v ::: _T) -> gamma |> (n :=: Flex v ::: _T))

infixl 5 <><
