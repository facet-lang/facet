{-# LANGUAGE UndecidableInstances #-}
module Text.Parser.Position
( PositionParsing(..)
, Pos
, Span(..)
, chainl1Loc
) where

import           Control.Applicative ((<**>), (<|>))
import qualified Facet.Carrier.Parser.Church as P
import           Facet.Span (Pos, Span(..))
import           Text.Parser.Combinators (Parsing)
import           Text.Parser.Token (Unhighlighted(..))

class Parsing p => PositionParsing p where
  position :: p Pos

instance P.Algebra sig m => PositionParsing (P.ParserC m) where
  position = P.position

instance PositionParsing p => PositionParsing (Unhighlighted p) where
  position = Unhighlighted position


chainl1Loc :: PositionParsing p => p a -> p (Span -> a -> a -> a) -> p a
chainl1Loc p op = scan where
  scan = (,) <$> position <*> p <**> rst
  rst = (\ f y end g (start, x) -> g (start, f (Span start end) x y)) <$> op <*> p <*> position <*> rst <|> pure snd
