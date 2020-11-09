module Facet.Context
( -- * Contexts
  Context(..)
, Entry(..)
, entryDef
, entryType
, empty
, (|>)
, level
, (!)
, lookupIndex
, Suffix
, (<><)
, restore
, replace
) where

import           Data.Foldable (foldl')
import           Facet.Name
import qualified Facet.Stack as S
import           Facet.Syntax
import           GHC.Stack
import           Prelude hiding (lookup)

newtype Context a = Context { elems :: S.Stack (Entry a) }

data Entry a
  -- FIXME: constructor names are unclear; Tm is typing, Ty is meta.
  -- FIXME: record implicitness in the context.
  -- FIXME: record sort in the context.
  = Tm Name a
  | Ty Meta (Maybe a) a

entryDef :: Entry a -> Maybe a
entryDef = \case
  Tm _   _ -> Nothing
  Ty _ v _ -> v

entryType :: Entry a -> a
entryType = \case
  Tm _   t -> t
  Ty _ _ t -> t


empty :: Context a
empty = Context S.Nil

(|>) :: Context a -> Entry a -> Context a
Context as |> a = Context (as S.:> a)

infixl 5 |>

level :: Context a -> Level
level (Context es) = go 0 es
  where
  go n S.Nil          = n
  go n (es S.:> Tm{}) = go (n + 1) es
  go n (es S.:> Ty{}) = go  n      es

(!) :: HasCallStack => Context a -> Index -> Entry a
Context es' ! Index i' = withFrozenCallStack $ go es' i'
  where
  go (es S.:> e@Tm{}) i
    | i == 0            = e
    | otherwise         = go es (i - 1)
  go (es S.:> _)      i = go es i
  go _                _ = error $ "Facet.Context.!: index (" <> show i' <> ") out of bounds (" <> show (length es') <> ")"

lookupIndex :: Name -> Context a -> Maybe (Index, a)
lookupIndex n = go (Index 0) . elems
  where
  go _ S.Nil          = Nothing
  go i (cs S.:> Tm n' t)
    | n == n'         = Just (i, t)
    | otherwise       = go (succ i) cs
  go i (cs S.:> Ty{}) = go i cs


type Suffix a = [Meta :=: Maybe a ::: a]

(<><) :: Context a -> Suffix a -> Context a
(<><) = foldl' (\ gamma (n :=: v ::: _T) -> gamma |> Ty n v _T)

infixl 5 <><

restore :: Applicative m => m (Maybe (Suffix a))
restore = pure Nothing

replace :: Applicative m => Suffix a -> m (Maybe (Suffix a))
replace a = pure (Just a)
