module Facet.REPL.Parser
( Command(..)
, meta
, Arg(..)
, parseCommands
) where

import Control.Applicative (Alternative(..))
import Data.Functor (void)
import Text.Parser.Char
import Text.Parser.Combinators
import Text.Parser.Position
import Text.Parser.Token hiding (brackets, comma)

data Command a = Command
  { symbols :: [String]
  , usage   :: String
  , value   :: Arg a
  }

meta :: Command a -> Maybe String
meta c = case value c of
  Meta s _ -> Just s
  _        -> Nothing

data Arg a
  = Pure a
  | Meta String (forall p . (PositionParsing p, Monad p) => p a)


parseCommands :: (PositionParsing p, Monad p) => [Command a] -> p a
parseCommands cs = choice (map go cs) <?> "command"
  where
  go c = parseSymbols (symbols c) *> parseValue (value c)
  parseSymbols = \case
    [] -> pure ()
    ss -> choice (map parseSymbol ss)
  parseSymbol s = void $ token (try (string (':':s) <* (eof <|> someSpace))) <?> (':':s)
  parseValue = \case
    Pure a   -> pure a
    Meta _ p -> p
