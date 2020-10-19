{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
module Facet.REPL.Parser
( Command(..)
, meta
, Value(..)
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
  , value   :: Value a
  }

meta :: Command a -> Maybe String
meta c = case value c of
  Meta s _ -> Just s
  _        -> Nothing

data Value a
  = Pure a
  | Meta String (forall p . (PositionParsing p, Monad p) => p a)


parseCommands :: (PositionParsing p, Monad p) => [Command a] -> p a
parseCommands = choice . map go
  where
  go c = parseSymbols (symbols c) *> parseValue (value c)
  parseSymbols = \case
    [] -> pure ()
    ss -> choice (map parseSymbol ss)
  parseSymbol s = void $ token (try (string (':':s) <* (eof <|> someSpace))) <?> (':':s)
  parseValue = \case
    Pure a   -> pure a
    Meta _ p -> p
