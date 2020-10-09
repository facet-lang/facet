module Facet.Error
( Err(..)
) where

import Control.Effect.Parser.Span (Span(..))
import Prettyprinter (Doc)
import Prettyprinter.Render.Terminal (AnsiStyle)

data Err = Err
  { span    :: Span
  , reason  :: Doc AnsiStyle
  , context :: [Doc AnsiStyle]
  }
