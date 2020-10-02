{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
module Facet.REPL
( repl
) where

import Control.Carrier.Empty.Church
import Control.Carrier.Parser.Church
import Control.Carrier.Readline.Haskeline
import Control.Effect.Parser.Notice (prettyNotice)
import Control.Effect.Parser.Span (Pos(..))
import Control.Monad.IO.Class (MonadIO)
import Data.Monoid (Alt(..))
import Facet.Pretty
import Prelude hiding (print)
import Prettyprinter as P hiding (column, width)
import Prettyprinter.Render.Terminal (AnsiStyle)
import Text.Parser.Combinators
import Text.Parser.Token hiding (comma)

repl :: IO ()
repl = runReadlineWithHistory loop

loop :: (Has Readline sig m, MonadIO m) => m ()
loop = do
  (line, resp) <- prompt "λ "
  case resp of
    Just resp -> case runParserWithString (Pos line 0) resp commandParser of
      Right cmd -> runEmpty (pure ()) (const loop) (runAction cmd)
      Left  err -> putDoc (prettyNotice err) *> loop
    Nothing   -> loop
  where
  commandParser = parseCommands commands

commands :: [Command Action]
commands = mconcat
  [ command ["help", "h", "?"] "display this list of commands" $ Action $ print helpDoc
  , command ["quit", "q"]      "exit the repl"                 $ Action $ empty
  ]

parseCommands :: TokenParsing m => [Command a] -> m a
parseCommands = getAlt . foldMap (Alt . go)
  where
  go (Command [] _ v) = pure v
  go (Command ss _ v) = v <$ choice (map (\ s -> symbol (':':s) <?> (':':s)) ss)


command :: [String] -> String -> a -> [Command a]
command s h a = [Command s h a]

data Command a = Command
  { symbols :: [String]
  , help    :: String
  , value   :: a
  }
  deriving (Foldable, Functor, Traversable)

newtype Action = Action { runAction :: forall sig m . (Has Empty sig m, Has Readline sig m) => m () }


helpDoc :: Doc AnsiStyle
helpDoc = tabulate2 (P.space <+> P.space) entries
  where
  entries = map entry commands
  entry c = (concatWith (surround (comma <> space)) (map (pretty . (':':)) (symbols c)), w (help c))
  w = align . fillSep . map pretty . words
