module Facet.TypeContext
( -- * Type contexts
  TypeContext(..)
) where

import           Facet.Functor.Synth
import           Facet.Kind
import           Facet.Name
import qualified Facet.Snoc as S

newtype TypeContext = TypeContext { getTypeContext :: S.Snoc (Name :==> Kind) }
