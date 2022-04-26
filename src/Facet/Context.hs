{-# LANGUAGE ExistentialQuantification #-}
module Facet.Context
( -- * Contexts
  Context(..)
, empty
, (|>)
, level
, (!)
, lookupIndex
, toEnv
) where

import qualified Control.Effect.Empty as E
import qualified Facet.Env as Env
import           Facet.Functor.Synth
import           Facet.Name
import qualified Facet.Snoc as S
import           Facet.Syntax
import           Facet.Type.Norm
import           GHC.Stack
import           Prelude hiding (lookup)

newtype Context = Context { elems :: Env.Env Type }


empty :: Context
empty = Context Env.empty

(|>) :: Context -> Name :==> Type -> Context
Context as |> a = Context (as Env.|> toEquation a)

infixl 5 |>

level :: Context -> Level
level (Context es) = Level (length es)

(!) :: HasCallStack => Context -> Index -> Name :==> Type
Context (Env.Env es') ! Index i' = withFrozenCallStack $ go es' i'
  where
  go (es S.:> e) i
    | i == 0       = fromEquation e
    | otherwise    = go es (i - 1)
  go _           _ = error $ "Facet.Context.!: index (" <> show i' <> ") out of bounds (" <> show (length es') <> ")"

lookupIndex :: E.Has E.Empty sig m => Name -> Context -> m (Index, Type)
lookupIndex n = go (Index 0) . Env.bindings . elems
  where
  go _ S.Nil       = E.empty
  go i (cs S.:> (n' :=: t))
    | n == n'   = pure (i, t)
    | otherwise = go (succ i) cs


toEnv :: Context -> Env.Env Type
toEnv = elems


toEquation :: a :==> b -> a :=: b
toEquation (a :==> b) = a :=: b

fromEquation :: a :=: b -> a :==> b
fromEquation (a :=: b) = a :==> b
