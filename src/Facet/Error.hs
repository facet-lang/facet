module Facet.Error
( Err(..)
, ErrDoc
) where

import Prettyprinter (Doc)
import Prettyprinter.Render.Terminal (AnsiStyle)

type ErrDoc = Doc AnsiStyle

data Err = Err
  { reason  :: ErrDoc
  , context :: [ErrDoc]
  }
