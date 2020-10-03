{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
module Facet.REPL
( repl
) where

import           Control.Carrier.Empty.Church
import           Control.Carrier.Parser.Church
import           Control.Carrier.Readline.Haskeline
import           Control.Carrier.State.Church
import           Control.Effect.Parser.Notice (Notice, prettyNotice)
import           Control.Effect.Parser.Span (Pos(..))
import qualified Data.Set as Set
import           Facet.Parser
import           Facet.Pretty
import           Facet.Print
import           Prelude hiding (print)
import           Prettyprinter as P hiding (column, width)
import           Prettyprinter.Render.Terminal (AnsiStyle)
import           Text.Parser.Combinators
import           Text.Parser.Token hiding (comma)

repl :: IO ()
repl
  = runReadlineWithHistory
  . evalState REPL{ files = mempty }
  $ loop

data REPL = REPL
  { files :: Set.Set FilePath
  }

loop :: (Has Readline sig m, Has (State REPL) sig m) => m ()
loop = do
  (line, resp) <- prompt "λ "
  case resp of
    -- FIXME: evaluate expressions
    Just resp -> case runParserWithString (Pos line 0) resp (runFacet 0 commandParser) of
      Right cmd -> runEmpty (pure ()) (const loop) (runAction cmd)
      Left  err -> print (prettyNotice err) *> loop
    Nothing   -> loop
  where
  commandParser = parseCommands commands

-- TODO:
-- - load
-- - reload
-- - multiline
commands :: [Command (Facet (ParserC (Either Notice))) Action]
commands =
  [ Command ["help", "h", "?"] "display this list of commands" . Pure $ Action $ print helpDoc
  , Command ["quit", "q"]      "exit the repl"                 . Pure $ Action $ empty
  , Command ["type", "t"]      "show the type of <expr>"       $ Meta "expr" type_
  , Command ["kind", "k"]      "show the kind of <type>"       $ Meta "type" kind_
  ]

type_, kind_ :: Facet (ParserC (Either Notice)) Action
type_ = let act e = Action (print (getPrint e)) in act <$> expr  -- FIXME: elaborate the expr & show the type
kind_ = let act e = Action (print (getPrint e)) in act <$> type' -- FIXME: elaborate the type & show the kind

parseCommands :: TokenParsing m => [Command m a] -> m a
parseCommands = choice . map go
  where
  go (Command [] _ v) = parseValue v
  go (Command ss _ v) = choice (map (\ s -> symbol (':':s) <?> (':':s)) ss) *> parseValue v
  parseValue = \case
    Pure a   -> pure a
    Meta _ p -> p


data Command p a = Command
  { symbols :: [String]
  , usage   :: String
  , value   :: Value p a
  }
  deriving (Foldable, Functor, Traversable)

meta :: Command p a -> Maybe String
meta c = case value c of
  Meta s _ -> Just s
  _        -> Nothing

data Value p a
  = Pure a
  | Meta String (p a)
  deriving (Foldable, Functor, Traversable)

newtype Action = Action { runAction :: forall sig m . (Has Empty sig m, Has Readline sig m) => m () }


helpDoc :: Doc AnsiStyle
helpDoc = tabulate2 (P.space <+> P.space) entries
  where
  entries = map entry commands
  entry c = (concatWith (surround (comma <> space)) (map (pretty . (':':)) (symbols c)) <> maybe mempty ((space <>) . enclose (pretty '<') (pretty '>') . pretty) (meta c), w (usage c))
  w = align . fillSep . map pretty . words
