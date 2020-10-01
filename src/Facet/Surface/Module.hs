module Facet.Surface.Module
( Module(..)
) where

import qualified Facet.Surface as S
import           Facet.Surface.Decl (Decl)

data Module
  = S.DName :.:. Decl
