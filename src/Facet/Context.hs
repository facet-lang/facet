module Facet.Context
( -- * Contexts
  Context(..)
, Entry(..)
, entryVar
, entryName
, entryType
, empty
, (|>)
, level
, (!?)
, (!)
, lookupIndex
, Suffix
, (<><)
, restore
, replace
) where

import           Data.Foldable (foldl')
import           Facet.Core
import           Facet.Name
import qualified Facet.Stack as S
import           Facet.Syntax
import           GHC.Stack
import           Prelude hiding (lookup)

newtype Context = Context { elems :: S.Stack Entry }

data Entry
  -- FIXME: constructor names are unclear; Tm is typing, Ty is meta.
  = Tm Int Name Type
  | Ty Int Name (Maybe Type) Type

entryVar :: Entry -> Int
entryVar = \case
  Tm v _   _ -> v
  Ty v _ _ _ -> v

entryName :: Entry -> Name
entryName = \case
  Tm _ n   _ -> n
  Ty _ n _ _ -> n

entryType :: Entry -> Type
entryType = \case
  Tm _ _   t -> t
  Ty _ _ _ t -> t


empty :: Context
empty = Context S.Nil

(|>) :: Context -> Entry -> Context
Context as |> a = Context (as S.:> a)

infixl 5 |>

level :: Context -> Level
level (Context c) = Level (length c)

(!?) :: Context -> Index -> Maybe Entry
c !? i = elems c S.!? getIndex i

(!) :: HasCallStack => Context -> Index -> Entry
c ! i = elems c S.! getIndex i

lookupIndex :: Name -> Context -> Maybe (Index, Type)
lookupIndex n = go (Index 0) . elems
  where
  go _ S.Nil           = Nothing
  go i (cs S.:> e)
    | n == entryName e = Just (i, entryType e)
    | otherwise        = go (succ i) cs


type Suffix = [(Int, Name) :=: Maybe Type ::: Type]

(<><) :: Context -> Suffix -> Context
(<><) = foldl' (\ gamma ((i, n) :=: v ::: _T) -> gamma |> Ty i n v _T)

infixl 5 <><

restore :: Applicative m => a -> m (a, Maybe Suffix)
restore = pure . (,Nothing)

replace :: Applicative m => Suffix -> a -> m (a, Maybe Suffix)
replace a = pure . (,Just a)
