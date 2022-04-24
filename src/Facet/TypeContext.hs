module Facet.TypeContext
( -- * Type contexts
  TypeContext(..)
, empty
) where

import           Facet.Functor.Synth
import           Facet.Kind
import           Facet.Name
import qualified Facet.Snoc as S

newtype TypeContext = TypeContext { getTypeContext :: S.Snoc (Name :==> Kind) }

empty :: TypeContext
empty = TypeContext S.Nil
