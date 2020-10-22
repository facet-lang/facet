module Facet.REPL.Parser
( Command(..)
, meta
, Arg(..)
, parseCommands
) where

import Control.Applicative (Alternative(..))
import Control.Monad (MonadPlus)
import Data.Functor (void)
import Facet.Effect.Parser
import Text.Parser.Char
import Text.Parser.Combinators
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
  | Meta String (forall sig p . (Has Parser sig p, MonadPlus p, TokenParsing p) => p a)


parseCommands :: (Has Parser sig p, MonadPlus p, TokenParsing p) => [Command a] -> p a
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
