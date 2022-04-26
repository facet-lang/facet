module Facet.Env
( Env(..)
, empty
, (|>)
, lookup
, index
, level
, (!)
, (!?)
) where

import           Control.Applicative ((<|>))
import           Control.Monad (guard)
import           Data.Maybe (fromMaybe)
import           Facet.Name
import qualified Facet.Snoc as S
import           Facet.Syntax
import           Fresnel.Getter (view)
import           GHC.Stack
import           Prelude hiding (lookup)

newtype Env v = Env { bindings :: S.Snoc (Name :=: v) }
  deriving (Foldable, Functor, Monoid, Semigroup, Traversable)

empty :: Env v
empty = Env S.Nil

(|>) :: Env v -> Name :=: v -> Env v
Env vs |> v = Env (vs S.:> v)

infixl 5 |>

lookup :: Env v -> Name -> Maybe v
lookup (Env vs) n = find (\ (n' :=: v) -> v <$ guard (n == n')) vs
  where
  find f = foldr ((<|>) . f) Nothing

index :: HasCallStack => Env v -> Name -> v
index env n = fromMaybe (error ("Env.index: name (" <> show n <> ") not found")) (lookup env n)

level :: Env v -> Level
level = Level . length . bindings

(!) :: HasCallStack => Env v -> Index -> v
Env env ! i = view def_ (env S.! getIndex i)

(!?) :: Env v -> Index -> Maybe v
Env env !? i = view def_ <$> (env S.!? getIndex i)
