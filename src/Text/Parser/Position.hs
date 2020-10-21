{-# LANGUAGE UndecidableInstances #-}
module Text.Parser.Position
( PositionParsing(..)
, Pos
, Span(..)
) where

import qualified Facet.Carrier.Parser.Church as P
import           Facet.Span (Pos, Span(..))
import           Text.Parser.Combinators (Parsing)
import           Text.Parser.Token (Unhighlighted(..), Unlined(..), Unspaced(..))

class Parsing p => PositionParsing p where
  position :: p Pos

instance P.Algebra sig m => PositionParsing (P.ParserC m) where
  position = P.position

instance PositionParsing p => PositionParsing (Unhighlighted p) where
  position = Unhighlighted position

instance PositionParsing p => PositionParsing (Unlined p) where
  position = Unlined position

instance PositionParsing p => PositionParsing (Unspaced p) where
  position = Unspaced position
