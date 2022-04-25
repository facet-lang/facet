module Facet.TypeContext
( -- * Type contexts
  TypeContext(..)
, empty
, (|>)
, lookupIndex
) where

import qualified Control.Effect.Empty as E
import           Facet.Functor.Synth
import           Facet.Kind
import           Facet.Name
import qualified Facet.Snoc as S

newtype TypeContext = TypeContext { getTypeContext :: S.Snoc (Name :==> Kind) }

empty :: TypeContext
empty = TypeContext S.Nil

(|>) :: TypeContext -> Name :==> Kind -> TypeContext
TypeContext as |> a = TypeContext (as S.:> a)

lookupIndex :: E.Has E.Empty sig m => Name -> TypeContext -> m (Index, Kind)
lookupIndex n = go (Index 0) . getTypeContext
  where
  go _ S.Nil    = E.empty
  go i (cs S.:> (n' :==> _K))
    | n == n'   = pure (i, _K)
    | otherwise = go (succ i) cs
