{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
module Facet.REPL
( repl
) where

import           Control.Applicative ((<|>))
import           Control.Carrier.Empty.Church
import           Control.Carrier.Error.Church
import           Control.Carrier.Parser.Church
import           Control.Carrier.Readline.Haskeline
import           Control.Carrier.State.Church
import           Control.Effect.Parser.Notice (Notice, prettyNotice)
import           Control.Effect.Parser.Span (Pos(..))
import           Control.Effect.Lens ((%=))
import           Control.Lens (Lens', lens)
import           Control.Monad.IO.Class
import           Data.Char
import           Data.Semigroup
import qualified Data.Set as Set
import           Facet.Parser
import           Facet.Pretty
import           Facet.Print
import           Prelude hiding (print)
import           Prettyprinter as P hiding (column, width)
import           Prettyprinter.Render.Terminal (AnsiStyle)
import           Text.Parser.Char hiding (space)
import           Text.Parser.Combinators
import           Text.Parser.Position
import           Text.Parser.Token hiding (comma)

repl :: IO ()
repl
  = runReadlineWithHistory
  . evalState REPL{ files = mempty }
  . evalEmpty
  $ loop

data REPL = REPL
  { files :: Set.Set FilePath
  }

files_ :: Lens' REPL (Set.Set FilePath)
files_ = lens files (\ r files -> r{ files })

loop :: (Has Empty sig m, Has Readline sig m, Has (State REPL) sig m, MonadIO m) => m ()
loop = do
  (line, resp) <- prompt "λ "
  runError (print . prettyNotice) pure $ case resp of
    -- FIXME: evaluate expressions
    Just resp -> runParserWithString (Pos line 0) resp (runFacet 0 (whole commandParser)) >>= runAction
    Nothing   -> pure ()
  loop
  where
  commandParser = parseCommands commands

  runAction = \case
    Help -> print helpDoc
    Quit -> empty
    Load path -> load path
    Type e -> print (getPrint e) -- FIXME: elaborate the expr & show the type
    Kind e -> print (getPrint e) -- FIXME: elaborate the type & show the kind


-- TODO:
-- - reload
-- - multiline
commands :: [Command Action]
commands =
  [ Command ["help", "h", "?"] "display this list of commands" $ Pure Help
  , Command ["quit", "q"]      "exit the repl"                 $ Pure Quit
  , Command ["load", "l"]      "add a module to the repl"      $ Meta "path" load_
  , Command ["type", "t"]      "show the type of <expr>"       $ Meta "expr" type_
  , Command ["kind", "k"]      "show the kind of <type>"       $ Meta "type" kind_
  ]

load_ :: PositionParsing p => p Action

load_ = Load <$> (stringLiteral <|> some (satisfy (not . isSpace)))

type_, kind_ :: (PositionParsing p, Monad p) => p Action

type_ = Type <$> runFacet 0 (whole expr ) -- FIXME: elaborate the expr & show the type
kind_ = Kind <$> runFacet 0 (whole type') -- FIXME: elaborate the type & show the kind


parseCommands :: (PositionParsing p, Monad p) => [Command a] -> p a
parseCommands = choice . map go
  where
  go c = parseSymbols (symbols c) *> parseValue (value c)
  parseSymbols = \case
    [] -> pure ""
    ss -> choice (map (\ s -> symbol (':':s) <?> (':':s)) ss)
  parseValue = \case
    Pure a   -> pure a
    Meta _ p -> p


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


data Action
  = Help
  | Quit
  | Load FilePath
  | Type Print
  | Kind Print

load :: (Has (Error Notice) sig m, Has Readline sig m, Has (State REPL) sig m, MonadIO m) => FilePath -> m ()
load path = do
  files_ %= Set.insert path
  runParserWithFile path (runFacet 0 (whole decl)) >>= print . getPrint

helpDoc :: Doc AnsiStyle
helpDoc = tabulate2 (stimes (3 :: Int) P.space) entries
  where
  entries = map entry commands
  entry c = (concatWith (surround (comma <> space)) (map (pretty . (':':)) (symbols c)) <> maybe mempty ((space <>) . enclose (pretty '<') (pretty '>') . pretty) (meta c), w (usage c))
  w = align . fillSep . map pretty . words
