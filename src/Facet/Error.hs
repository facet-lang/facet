module Facet.Error
( ErrDoc
, Err(..)
) where

import Prettyprinter (Doc)
import Prettyprinter.Render.Terminal (AnsiStyle)

type ErrDoc = Doc AnsiStyle

data Err = Err
  { reason  :: ErrDoc
  , context :: [ErrDoc]
  }
  deriving (Show)
