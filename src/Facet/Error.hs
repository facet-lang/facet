module Facet.Error
( Err(..)
) where

import Prettyprinter (Doc)
import Prettyprinter.Render.Terminal (AnsiStyle)

data Err = Err
  { reason  :: Doc AnsiStyle
  , context :: [Doc AnsiStyle]
  }
