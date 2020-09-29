module Text.Parser.Location
( LocationParsing(..)
, spanned
) where

import Control.Effect.Parser.Span (Pos, Span(..))
import Text.Parser.Token (TokenParsing)

class TokenParsing p => LocationParsing p where
  position :: p Pos

spanned :: LocationParsing p => p a -> p (Span, a)
spanned p = mk <$> position <*> p <*> position
  where
  mk s a e = (Span s e, a)
