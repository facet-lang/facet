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
, toEnv
, evalIn
, Suffix
, (<><)
, restore
, replace
  -- * Metacontexts
, Subst(..)
) where

import           Data.Foldable (foldl')
import qualified Data.IntMap as IntMap
import           Data.Maybe (fromMaybe)
import           Facet.Core.Type
import           Facet.Name
import qualified Facet.Stack as S
import           Facet.Syntax
import           GHC.Stack
import           Prelude hiding (lookup)

newtype Context = Context { elems :: S.Stack Entry }

data Entry
  -- FIXME: record implicitness in the context.
  = Rigid Name Type
  | Flex Meta (Maybe Type) Type

entryDef :: Entry -> Maybe Type
entryDef = \case
  Rigid{}    -> Nothing
  Flex _ v _ -> v

entryType :: Entry -> Type
entryType = \case
  Rigid   _ t -> t
  Flex  _ _ t -> t


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
  go n (es S.:> Flex{})  = go  n      es

(!) :: HasCallStack => Context -> Index -> Entry
Context es' ! Index i' = withFrozenCallStack $ go es' i'
  where
  go (es S.:> e@Rigid{}) i
    | i == 0               = e
    | otherwise            = go es (i - 1)
  go (es S.:> _)         i = go es i
  go _                   _ = error $ "Facet.Context.!: index (" <> show i' <> ") out of bounds (" <> show (length es') <> ")"

lookupIndex :: Name -> Context -> Maybe (Index, Type)
lookupIndex n = go (Index 0) . elems
  where
  go _ S.Nil            = Nothing
  go i (cs S.:> Rigid n' t)
    | n == n'           = Just (i, t)
    | otherwise         = go (succ i) cs
  go i (cs S.:> Flex{}) = go i cs


-- | Construct an environment suitable for evaluation from a 'Context'.
toEnv :: Context -> (IntMap.IntMap Type, S.Stack Type)
toEnv c = (metas (elems c), locals 0 (elems c))
  where
  d = level c
  locals i = \case
    S.Nil           -> S.Nil
    bs S.:> Rigid{} -> locals (succ i) bs S.:> free (indexToLevel d i)
    bs S.:> Flex{}  -> locals i bs
  metas = \case
    S.Nil              -> mempty
    bs S.:> Rigid{}    -> metas bs
    bs S.:> Flex m v _ -> IntMap.insert (getMeta m) (fromMaybe (metavar m) v) (metas bs)

evalIn :: Context -> TExpr -> Type
evalIn = uncurry eval . toEnv


type Suffix = [Meta :=: Maybe Type ::: Type]

(<><) :: Context -> Suffix -> Context
(<><) = foldl' (\ gamma (n :=: v ::: _T) -> gamma |> Flex n v _T)

infixl 5 <><

restore :: Applicative m => m (Maybe Suffix)
restore = pure Nothing

replace :: Applicative m => Suffix -> m (Maybe Suffix)
replace a = pure (Just a)


newtype Subst = Subst (IntMap.IntMap (Maybe Type ::: Type))
