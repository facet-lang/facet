module Facet.REPL.Parser
( Command(..)
, command
, parseCommands
, parseCommand
, CommandParser(..)
) where

import Control.Algebra
import Control.Applicative (Alternative(..))
import Control.Effect.Sum
import Control.Monad (ap, liftM, void)
import Facet.Effect.Parser
import Text.Parser.Char
import Text.Parser.Combinators
import Text.Parser.Token hiding (brackets, comma)

data Command a = Command
  { symbols :: [String]
  , usage   :: String
  , meta    :: Maybe String
  , parse   :: CommandParser a
  }

command :: [String] -> String -> Maybe String -> CommandParser a -> Command a
command = Command

parseCommands :: (Has Parser sig p, TokenParsing p) => [Command a] -> p a
parseCommands cs = choice (map parseCommand cs) <?> "command"

parseCommand :: (Has Parser sig p, TokenParsing p) => Command a -> p a
parseCommand c = parseSymbols (symbols c) *> runCommandParser (parse c)
  where
  parseSymbols = \case
    [] -> pure ()
    ss -> choice (map parseSymbol ss)
  parseSymbol s = void $ token (try (string (':':s) <* (eof <|> someSpace))) <?> (':':s)


newtype CommandParser a = CommandParser { runCommandParser :: (forall sig p . (Has Parser sig p, TokenParsing p) => p a) }

instance Functor CommandParser where
  fmap = liftM

instance Applicative CommandParser where
  pure a = CommandParser $ pure a
  (<*>) = ap

instance Alternative CommandParser where
  empty = CommandParser empty
  CommandParser a <|> CommandParser b = CommandParser (a <|> b)
  many (CommandParser m) = CommandParser (many m)
  some (CommandParser m) = CommandParser (some m)

instance Monad CommandParser where
  m >>= f = CommandParser (runCommandParser m >>= runCommandParser . f)

instance Algebra Parser CommandParser where
  alg hdl sig ctx = CommandParser $ alg (runCommandParser . hdl) (inj sig) ctx

instance Parsing CommandParser where
  try (CommandParser m) = CommandParser (try m)
  CommandParser m <?> s = CommandParser (m <?> s)
  skipMany (CommandParser m) = CommandParser (skipMany m)
  skipSome (CommandParser m) = CommandParser (skipSome m)
  unexpected s = CommandParser (unexpected s)
  eof = CommandParser eof
  notFollowedBy (CommandParser m) = CommandParser (notFollowedBy m)

instance CharParsing CommandParser where
  satisfy p = CommandParser (satisfy p)
  char c = CommandParser (char c)
  notChar c = CommandParser (notChar c)
  anyChar = CommandParser anyChar
  string s = CommandParser (string s)
  text s = CommandParser (text s)

instance TokenParsing CommandParser where
  someSpace = CommandParser someSpace
  nesting (CommandParser m) = CommandParser (nesting m)
  semi = CommandParser semi
  highlight h (CommandParser m) = CommandParser (highlight h m)
  token (CommandParser m) = CommandParser (token m)
