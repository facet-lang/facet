module Facet.Context
( -- * Contexts
  Context(..)
, Entry(..)
, entryType
, empty
, (|>)
, level
, (!)
, lookupIndex
, toEnv
) where

import           Facet.Core.Type
import           Facet.Name
import qualified Facet.Stack as S
import           GHC.Stack
import           Prelude hiding (lookup)

newtype Context = Context { elems :: S.Stack Entry }

data Entry
  -- FIXME: record implicitness in the context.
  = Rigid Name Type

entryType :: Entry -> Type
entryType = \case
  Rigid   _ t -> t


empty :: Context
empty = Context S.Nil

(|>) :: Context -> Entry -> Context
Context as |> a = Context (as S.:> a)

infixl 5 |>

level :: Context -> Level
level (Context es) = go 0 es
  where
  go n S.Nil             = n
  go n (es S.:> Rigid{}) = go (n + 1) es

(!) :: HasCallStack => Context -> Index -> Entry
Context es' ! Index i' = withFrozenCallStack $ go es' i'
  where
  go (es S.:> e@Rigid{}) i
    | i == 0               = e
    | otherwise            = go es (i - 1)
  go _                   _ = error $ "Facet.Context.!: index (" <> show i' <> ") out of bounds (" <> show (length es') <> ")"

lookupIndex :: Name -> Context -> Maybe (Index, Type)
lookupIndex n = go (Index 0) . elems
  where
  go _ S.Nil            = Nothing
  go i (cs S.:> Rigid n' t)
    | n == n'           = Just (i, t)
    | otherwise         = go (succ i) cs


-- | Construct an environment suitable for evaluation from a 'Context'.
toEnv :: Context -> S.Stack Type
toEnv c = locals 0 (elems c)
  where
  d = level c
  locals i = \case
    S.Nil           -> S.Nil
    bs S.:> Rigid{} -> locals (succ i) bs S.:> free (indexToLevel d i)
