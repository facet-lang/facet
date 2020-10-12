module Facet.Error
( ErrDoc
, Err(..)
) where

import Control.Effect.Parser.Span (Span)
import Prettyprinter (Doc)
import Prettyprinter.Render.Terminal (AnsiStyle)

type ErrDoc = Doc AnsiStyle

data Err = Err
  { span    :: Span
  , reason  :: ErrDoc
  , context :: [ErrDoc]
  }
  deriving (Show)
