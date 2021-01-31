module Facet.Context
( -- * Contexts
  Context(..)
, Entry(..)
, empty
, (|>)
, level
, (!)
, lookupIndex
, toEnv
) where

import           Data.Semialign
import           Facet.Core.Type
import           Facet.Name
import           Facet.Semiring
import qualified Facet.Stack as S
import           GHC.Stack
import           Prelude hiding (lookup, zipWith)

newtype Context = Context { elems :: S.Stack Entry }

-- | A precondition for use of this instance is that one only ever '<>'s 'Context's assigning the same types to the same variables in the same order.
instance Semigroup Context where
  Context e1 <> Context e2 = Context (zipWith combine e1 e2) where
    combine (Entry _ q1 _) (Entry n q2 _T) = Entry n (q1 <> q2) _T

data Entry = Entry
  { name     :: Name
  , quantity :: Tropical Integer
  , type'    :: Type
  }

empty :: Context
empty = Context S.Nil

(|>) :: Context -> Entry -> Context
Context as |> a = Context (as S.:> a)

infixl 5 |>

level :: Context -> Level
level (Context es) = Level (length es)

(!) :: HasCallStack => Context -> Index -> Entry
Context es' ! Index i' = withFrozenCallStack $ go es' i'
  where
  go (es S.:> e) i
    | i == 0       = e
    | otherwise    = go es (i - 1)
  go _           _ = error $ "Facet.Context.!: index (" <> show i' <> ") out of bounds (" <> show (length es') <> ")"

lookupIndex :: Name -> Context -> Maybe (Index, Type)
lookupIndex n = go (Index 0) . elems
  where
  go _ S.Nil            = Nothing
  go i (cs S.:> Entry n' _ t)
    | n == n'           = Just (i, t)
    | otherwise         = go (succ i) cs


-- | Construct an environment suitable for evaluation from a 'Context'.
toEnv :: Context -> S.Stack Type
toEnv c = locals 0 (elems c)
  where
  d = level c
  locals i = \case
    S.Nil     -> S.Nil
    bs S.:> _ -> locals (succ i) bs S.:> free (indexToLevel d i)
