{-# LANGUAGE ExistentialQuantification #-}
module Facet.Context
( -- * Contexts
  Context(..)
, Binding(..)
, empty
, (|>)
, level
, (!)
, lookupIndex
, toEnv
) where

import qualified Control.Effect.Empty as E
import           Data.Foldable (find, toList)
import qualified Facet.Env as Env
import           Facet.Functor.Synth
import           Facet.Kind (Kind)
import           Facet.Name
import           Facet.Pattern
import qualified Facet.Snoc as S
import           Facet.Syntax
import           Facet.Type.Norm
import           Fresnel.Review (review)
import           GHC.Stack
import           Prelude hiding (lookup)

newtype Context = Context { elems :: S.Snoc Binding }

data Binding
  = Type (Pattern (Name :==> Type))
  | Kind (Name :==> Kind)


empty :: Context
empty = Context S.Nil

(|>) :: Context -> Binding -> Context
Context as |> a = Context (as S.:> a)

infixl 5 |>

level :: Context -> Level
level (Context es) = Level (length es)

(!) :: HasCallStack => Context -> Index -> Binding
Context es' ! Index i' = withFrozenCallStack $ go es' i'
  where
  go (es S.:> e) i
    | i == 0       = e
    | otherwise    = go es (i - 1)
  go _           _ = error $ "Facet.Context.!: index (" <> show i' <> ") out of bounds (" <> show (length es') <> ")"

lookupIndex :: E.Has E.Empty sig m => Name -> Context -> m (LName Index, Either Kind Type)
lookupIndex n = go (Index 0) . elems
  where
  go _ S.Nil       = E.empty
  go i (cs S.:> b) = case b of
    Type p
      | Just (n' :==> t) <- find ((== n) . proof) p -> pure (LName i n', Right t)
    Kind (n' :==> k)
      | n == n'                                     -> pure (LName i n', Left k)
    _                                               -> go (succ i) cs


toEnv :: Context -> Env.Env Type
toEnv c = Env.Env (S.fromList (zipWith toType (toList (elems c)) [0..pred (level c)]))
  where
  toType b d = case b of
    Type p          -> (\ b -> proof b :=: bind d (proof b)) <$> p
    Kind (n :==> _) -> review _PVar (n :=: bind d n)

  bind d b = free (LName d b)
