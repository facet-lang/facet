{-# LANGUAGE UndecidableInstances #-}
module Text.Parser.Position
( PositionParsing(..)
, Pos
, Span(..)
, spanning
, chainl1Loc
) where

import           Control.Applicative ((<**>), (<|>))
import qualified Facet.Carrier.Parser.Church as P
import           Facet.Span (Pos, Span(..))
import           Text.Parser.Combinators (Parsing)

class Parsing p => PositionParsing p where
  position :: p Pos

instance P.Algebra sig m => PositionParsing (P.ParserC m) where
  position = P.position

spanning :: PositionParsing p => p a -> p Span
spanning p = Span <$> position <* p <*> position


chainl1Loc :: PositionParsing p => p a -> p (Span -> a -> a -> a) -> p a
chainl1Loc p op = scan where
  scan = (,) <$> position <*> p <**> rst
  rst = (\ f y end g (start, x) -> g (start, f (Span start end) x y)) <$> op <*> p <*> position <*> rst <|> pure snd
