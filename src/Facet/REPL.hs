{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Facet.REPL
( repl
) where

import Control.Carrier.Empty.Church
import Control.Carrier.Parser.Church
import Control.Carrier.Readline.Haskeline
import Control.Effect.Parser.Notice (prettyNotice)
import Control.Effect.Parser.Span (Pos(..))
import Control.Monad.IO.Class (MonadIO)
import Data.Bifunctor (bimap)
import Data.Monoid (Alt(..))
import Facet.Pretty
import Prelude hiding (print)
import Prettyprinter as P hiding (column, width)
import Prettyprinter.Render.Terminal (AnsiStyle)
import Text.Parser.Char
import Text.Parser.Combinators
import Text.Parser.Token

repl :: IO ()
repl = runReadlineWithHistory loop

loop :: (Has Readline sig m, MonadIO m) => m ()
loop = do
  (line, resp) <- prompt "λ "
  case resp of
    Just resp -> case runParserWithString (Pos line 0) resp commandParser of
      Right cmd -> runEmpty (pure ()) (const loop) cmd
      Left  err -> putDoc (prettyNotice err) *> loop
    Nothing   -> loop
  where
  commandParser = parseCommands commands

commands :: (Has Empty sig m, Has Readline sig m) => [Command (m ())]
commands = mconcat
  [ command ["help", "h", "?"] "display this list of commands" $ print helpDoc
  , command ["quit", "q"]      "exit the repl"                 $ empty
  ]

parseCommands :: TokenParsing m => [Command a] -> m a
parseCommands = getAlt . foldMap (Alt . go)
  where
  go (Command [] _ v) = pure v
  go (Command ss _ v) = v <$ token (char ':' *> choice (map string ss))


command :: [String] -> String -> a -> [Command a]
command s h a = [Command s h a]

data Command a = Command
  { symbols :: [String]
  , help    :: String
  , value   :: a
  }
  deriving (Foldable, Functor, Traversable)


helpDoc :: Doc AnsiStyle
helpDoc = tabulate2 (P.space <+> P.space) (map (bimap pretty w) entries)
  where
  entries =
    [ (":help, :h, :?", "display this list of commands")
    , (":quit, :q",     "exit the repl")
    ]
  w = align . fillSep . map pretty . words
