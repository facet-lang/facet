{-# LANGUAGE LambdaCase #-}
module Facet.REPL
( repl
) where

import Control.Applicative ((<|>))
import Control.Carrier.Empty.Church
import Control.Carrier.Parser.Church
import Control.Carrier.Readline.Haskeline
import Control.Effect.Parser.Notice (prettyNotice)
import Control.Effect.Parser.Span (Pos(..))
import Control.Monad.IO.Class (MonadIO)
import Facet.Pretty
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
      Right cmd -> runEmpty (pure ()) (const loop) (interpret cmd)
      Left  err -> putDoc (prettyNotice err) *> loop
    Nothing   -> loop

interpret :: Has Empty sig m => Command -> m ()
interpret = \case
  Quit -> empty

commandParser :: TokenParsing m => m Command
commandParser = char ':' *> choice
  [ Quit <$ command 'q' "quit"
  ]

data Command
  = Quit

command :: TokenParsing m => Char -> String -> m ()
command s l
  =   () <$ symbolic s
  <|> () <$ symbol l
