{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
module Facet.REPL
( repl
) where

import           Control.Applicative ((<|>))
import           Control.Carrier.Empty.Church
import           Control.Carrier.Error.Church
import           Control.Carrier.Parser.Church
import           Control.Carrier.Readline.Haskeline
import           Control.Carrier.State.Church
import           Control.Effect.Lens (use, (%=))
import           Control.Effect.Parser.Notice (prettyNoticeWith)
import           Control.Lens (Lens', lens)
import           Control.Monad.IO.Class
import           Data.Char
import           Data.Foldable (for_)
import qualified Data.Map as Map
import           Data.Semigroup
import           Data.Text.Lazy (unpack)
import           Facet.Algebra
import qualified Facet.Elab as Elab
import qualified Facet.Env as Env
import           Facet.Notice
import           Facet.Parser
import           Facet.Pretty
import           Facet.Print
import           Facet.REPL.Parser
import           Facet.Stack
import           Facet.Surface (Expr, Type)
import           Prelude hiding (print)
import           Silkscreen hiding (column, line, width)
import qualified System.Console.ANSI as ANSI
import           Text.Parser.Char hiding (space)
import           Text.Parser.Combinators
import           Text.Parser.Position
import           Text.Parser.Token hiding (brackets, comma)

repl :: IO ()
repl
  = runReadlineWithHistory
  . evalState REPL{ line = 0, files = mempty, promptFunction = defaultPromptFunction, env = mempty }
  . evalEmpty
  $ loop

defaultPromptFunction :: Int -> IO String
defaultPromptFunction _ = pure $ "\ESC]0;facet\x7" <> cyan <> "λ " <> plain
  where
  cyan = "\ESC[1;36m\STX"
  plain = "\ESC[0m\STX"


data REPL = REPL
  { line           :: Int
  , files          :: Map.Map FilePath File
  , promptFunction :: Int -> IO String
  , env            :: Env.Env Elab.Type
  }

data File = File
  { loaded :: Bool
  }

line_ :: Lens' REPL Int
line_ = lens line (\ r line -> r{ line })

files_ :: Lens' REPL (Map.Map FilePath File)
files_ = lens files (\ r files -> r{ files })

env_ :: Lens' REPL (Env.Env Elab.Type)
env_ = lens env (\ r env -> r{ env })

loop :: (Has Empty sig m, Has Readline sig m, Has (State REPL) sig m, MonadIO m) => m ()
loop = do
  (line, resp) <- prompt
  runError (print . prettyNoticeWith sgrStyle) pure $ case resp of
    -- FIXME: evaluate expressions
    Just resp -> rethrowParseErrors (runParserWithString line resp (runFacet [] (whole commandParser))) >>= runAction
    Nothing   -> pure ()
  loop
  where
  commandParser = parseCommands commands

  runAction = \case
    Help -> print helpDoc
    Quit -> empty
    Load path -> load path
    Reload -> reload
    Type e -> print (getPrint (foldSExpr surface Nil e)) -- FIXME: elaborate the expr & show the type
    Kind t -> print (getPrint (foldSType surface Nil t)) -- FIXME: elaborate the type & show the kind


-- TODO:
-- - multiline
commands :: [Command Action]
commands =
  [ Command ["help", "h", "?"]  "display this list of commands" $ Pure Help
  , Command ["quit", "q"]       "exit the repl"                 $ Pure Quit
  , Command ["load", "l"]       "add a module to the repl"      $ Meta "path" load_
  , Command ["reload", "r", ""] "reload the loaded modules"     $ Pure Reload
  , Command ["type", "t"]       "show the type of <expr>"       $ Meta "expr" type_
  , Command ["kind", "k"]       "show the kind of <type>"       $ Meta "type" kind_
  ]

load_ :: PositionParsing p => p Action

load_ = Load <$> (stringLiteral <|> some (satisfy (not . isSpace)))

type_, kind_ :: (PositionParsing p, Monad p) => p Action

type_ = Type <$> runFacet [] (whole expr )
kind_ = Kind <$> runFacet [] (whole type')


data Action
  = Help
  | Quit
  | Load FilePath
  | Reload
  | Type (Spanned Expr)
  | Kind (Spanned Type)

load :: (Has (Error (Notice [ANSI.SGR])) sig m, Has Readline sig m, Has (State REPL) sig m, MonadIO m) => FilePath -> m ()
load path = do
  files_ %= Map.insert path File{ loaded = False }
  rethrowParseErrors (runParserWithFile path (runFacet [] (whole module'))) >>= print . getPrint . foldSModule surface

reload :: (Has (Error (Notice [ANSI.SGR])) sig m, Has Readline sig m, Has (State REPL) sig m, MonadIO m) => m ()
reload = do
  files <- use files_
  -- FIXME: topological sort
  let ln = length files
  for_ (zip [(1 :: Int)..] (Map.keys files)) $ \ (i, path) -> do
    -- FIXME: module name
    print $ annotate [ANSI.SetColor ANSI.Foreground ANSI.Vivid ANSI.Green] (brackets (pretty i <+> pretty "of" <+> pretty ln)) <+> nest 2 (group (fillSep [ pretty "Loading", pretty path ]))
    rethrowParseErrors (runParserWithFile path (runFacet [] (whole module')) >>= print . getPrint . foldSModule surface) `catchError` \ n -> print (indent 2 (prettyNoticeWith sgrStyle n))

helpDoc :: Doc [ANSI.SGR]
helpDoc = tabulate2 (stimes (3 :: Int) space) entries
  where
  entries = map entry commands
  entry c = (concatWith (surround (comma <> space)) (map (pretty . (':':)) (symbols c)) <> maybe mempty ((space <>) . enclose (pretty '<') (pretty '>') . pretty) (meta c), w (usage c))
  w = align . fillSep . map pretty . words


prompt :: (Has Readline sig m, Has (State REPL) sig m, MonadIO m) => m (Int, Maybe String)
prompt = do
  line <- gets line
  line_ %= (+ 1)
  fn <- gets promptFunction
  p <- liftIO $ fn line
  (,) line <$> getInputLine p

print :: (Has Readline sig m, MonadIO m) => Doc [ANSI.SGR] -> m ()
print d = do
  opts <- liftIO layoutOptionsForTerminal
  outputStrLn (unpack (renderLazy (layoutSmart opts d)))
