{-# LANGUAGE UndecidableInstances #-}
module Text.Parser.Location
( LocationParsing(..)
, Pos
, Span
, spanned
) where

import qualified Control.Carrier.Parser.Church as P
import           Control.Effect.Parser.Span (Pos, Span(..))
import           Text.Parser.Token (TokenParsing)

class TokenParsing p => LocationParsing p where
  position :: p Pos

instance P.Algebra sig m => LocationParsing (P.ParserC m) where
  position = P.position

spanned :: LocationParsing p => p a -> p (Span, a)
spanned p = mk <$> position <*> p <*> position
  where
  mk s a e = (Span s e, a)
