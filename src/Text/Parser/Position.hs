{-# LANGUAGE UndecidableInstances #-}
module Text.Parser.Position
( LocationParsing(..)
, Pos
, Span
, spanning
, spanned
) where

import qualified Control.Carrier.Parser.Church as P
import           Control.Effect.Parser.Span (Pos, Span(..))
import           Text.Parser.Token (TokenParsing)

class TokenParsing p => LocationParsing p where
  position :: p Pos

instance P.Algebra sig m => LocationParsing (P.ParserC m) where
  position = P.position

spanning :: LocationParsing p => p a -> p Span
spanning p = Span <$> position <* p <*> position

spanned :: LocationParsing p => p a -> p (Span, a)
spanned p = mk <$> position <*> p <*> position
  where
  mk s a e = (Span s e, a)
