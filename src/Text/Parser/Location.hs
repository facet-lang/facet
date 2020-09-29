module Text.Parser.Location
( LocationParsing(..)
) where

import Control.Effect.Parser.Span (Pos)
import Text.Parser.Token (TokenParsing)

class TokenParsing p => LocationParsing p where
  position :: p Pos
