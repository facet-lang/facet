module Facet.REPL.Parser
( Command(..)
, command
, parseCommands
, Commands(..)
, CommandParser(..)
) where

import Control.Algebra
import Control.Applicative (Alternative(..))
import Control.Effect.Sum
import Control.Monad (void)
import Facet.Effect.Parser
import Text.Parser.Char
import Text.Parser.Combinators
import Text.Parser.Token hiding (brackets, comma)

data Command = Command
  { symbols :: [String]
  , usage   :: String
  , meta    :: Maybe String
  }

command :: [String] -> String -> Maybe String -> (forall sig p . (Has Parser sig p, TokenParsing p) => p a) -> Commands a
command symbols usage meta parse = Commands
  [Command symbols usage meta]
  (parseSymbols symbols *> runCommandParser parse)
  where
  parseSymbols = \case
    [] -> pure ()
    ss -> choice (map parseSymbol ss)
  parseSymbol s = void $ token (try (string (':':s) <* (eof <|> someSpace))) <?> (':':s)


parseCommands :: (Has Parser sig p, TokenParsing p) => Commands a -> p a
parseCommands = runCommandParser . _parseCommands

data Commands a = Commands
  { getCommands    :: [Command]
  , _parseCommands :: CommandParser a
  }
  deriving (Functor)

instance Applicative Commands where
  pure a = Commands [] (pure a)
  Commands c1 p1 <*> Commands c2 p2 = Commands (c1 <> c2) (p1 <*> p2)

instance Alternative Commands where
  empty = Commands [] empty
  Commands c1 p1 <|> Commands c2 p2 = Commands (c1 <> c2) (p1 <|> p2)


newtype CommandParser a = CommandParser { runCommandParser :: (forall sig p . (Has Parser sig p, TokenParsing p) => p a) }

instance Functor CommandParser where
  fmap f (CommandParser m) = CommandParser (fmap f m)

instance Applicative CommandParser where
  pure a = CommandParser $ pure a
  CommandParser f <*> CommandParser a = CommandParser (f <*> a)

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
