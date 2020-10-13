module Facet.Print.Applicative
( space
) where

import           Silkscreen (Printer)
import qualified Silkscreen as S

space :: (Applicative f, Printer p) => f p
space = pure S.space
