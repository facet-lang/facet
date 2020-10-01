{-# LANGUAGE UndecidableInstances #-}
module Text.Parser.Location
( LocationParsing(..)
, Pos
, Span
, spanning
, spanned
) where

import qualified Control.Carrier.Parser.Church as P
import           Control.Monad (MonadPlus(..))
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.Reader (ReaderT(..))
import           Control.Effect.Parser.Span (Pos, Span(..))
import           Text.Parser.Token (TokenParsing)

class TokenParsing p => LocationParsing p where
  position :: p Pos

instance P.Algebra sig m => LocationParsing (P.ParserC m) where
  position = P.position

instance (LocationParsing m, MonadPlus m) => LocationParsing (ReaderT r m) where
  position = lift position

spanning :: LocationParsing p => p a -> p Span
spanning p = Span <$> position <* p <*> position

spanned :: LocationParsing p => p a -> p (Span, a)
spanned p = mk <$> position <*> p <*> position
  where
  mk s a e = (Span s e, a)
