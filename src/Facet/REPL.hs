{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
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
import           Control.Carrier.Reader
import           Control.Carrier.Readline.Haskeline
import           Control.Carrier.State.Church
import           Control.Effect.Lens (use, (%=))
import           Control.Effect.Parser.Source (Source(..), sourceFromString)
import           Control.Lens (Lens', lens)
import           Control.Monad.IO.Class
import           Data.Char
import           Data.Foldable (for_)
import qualified Data.Map as Map
import           Data.Semigroup
import           Data.Text.Lazy (unpack)
import           Facet.Algebra hiding (Algebra)
import qualified Facet.Carrier.State.Lens as L
import qualified Facet.Carrier.Throw.Inject as I
import qualified Facet.Elab as Elab
import qualified Facet.Env as Env
import           Facet.Notice
import           Facet.Parser
import           Facet.Pretty
import           Facet.Print
import           Facet.REPL.Parser
import           Facet.Stack
import           Facet.Surface (Expr, Type)
import           Facet.Syntax
import           Prelude hiding (print, span)
import           Silkscreen hiding (line)
import           System.Console.ANSI
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
defaultPromptFunction _ = pure $ setTitleCode "facet" <> cyan <> "λ " <> plain
  where
  cyan = setSGRCode [SetColor Foreground Vivid Cyan]
  plain = setSGRCode []


data REPL = REPL
  { line           :: Int
  , files          :: Map.Map FilePath File
  , promptFunction :: Int -> IO String
  , env            :: Env.Env Elab.Type
  }

line_ :: Lens' REPL Int
line_ = lens line (\ r line -> r{ line })

files_ :: Lens' REPL (Map.Map FilePath File)
files_ = lens files (\ r files -> r{ files })

env_ :: Lens' REPL (Env.Env Elab.Type)
env_ = lens env (\ r env -> r{ env })


data File = File
  { loaded :: Bool
  }

loaded_ :: Lens' File Bool
loaded_ = lens loaded (\ f loaded-> f{ loaded })


loop :: (Has Empty sig m, Has Readline sig m, Has (State REPL) sig m, MonadIO m) => m ()
loop = do
  resp <- prompt
  runError (print . prettyNotice) pure $ case resp of
    -- FIXME: evaluate expressions
    Just src -> rethrowParseErrors (runParserWithSource src (runFacet [] (whole commandParser))) >>= runAction src
    Nothing  -> pure ()
  loop
  where
  commandParser = parseCommands commands

  runAction src = \case
    Help -> print helpDoc
    Quit -> empty
    Load path -> load path
    Reload -> reload
    Type e -> do
      _ ::: _T <- elab src $ Elab.elabWith (\ s (e ::: _T) -> (:::) <$> Elab.apply s e <*> Elab.apply s _T) (Elab.elabExpr e Nothing)
      print (getPrint (ann (foldSExpr surface Nil e ::: foldCValue surface Nil _T)))
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

load :: (Has (Error (Notice [SGR])) sig m, Has Readline sig m, Has (State REPL) sig m, MonadIO m) => FilePath -> m ()
load path = do
  files_ %= Map.insert path File{ loaded = False }
  reload

reload :: (Has (Error (Notice [SGR])) sig m, Has Readline sig m, Has (State REPL) sig m, MonadIO m) => m ()
reload = do
  files <- use files_
  -- FIXME: topological sort
  let ln = length files
  for_ (zip [(1 :: Int)..] (Map.keys files)) $ \ (i, path) -> do
    -- FIXME: check whether files need reloading
    -- FIXME: module name
    print $ success (brackets (pretty i <+> pretty "of" <+> pretty ln)) <+> nest 2 (group (fillSep [ pretty "Loading", pretty path ]))
    rethrowParseErrors (do
      m <- runParserWithFile path (runFacet [] (whole module'))
      print $ getPrint (foldSModule surface m))
      `catchError` \ n ->
        print (indent 2 (prettyNotice n))

success :: Doc [SGR] -> Doc [SGR]
success = annotate [SetColor Foreground Vivid Green]

helpDoc :: Doc [SGR]
helpDoc = tabulate2 (stimes (3 :: Int) space) (map entry commands)
  where
  entry c =
    ( concatWith (surround (comma <> space)) (map (pretty . (':':)) (symbols c)) <> maybe mempty ((space <>) . enclose (pretty '<') (pretty '>') . pretty) (meta c)
    , w (usage c))
  w = align . fillSep . map pretty . words


prompt :: (Has Readline sig m, Has (State REPL) sig m, MonadIO m) => m (Maybe Source)
prompt = do
  line <- gets line
  line_ %= (+ 1)
  fn <- gets promptFunction
  p <- liftIO $ fn line
  fmap (sourceFromString Nothing line) <$> getInputLine p

print :: (Has Readline sig m, MonadIO m) => Doc [SGR] -> m ()
print d = do
  opts <- liftIO layoutOptionsForTerminal
  outputStrLn (unpack (renderLazy (layoutSmart opts d)))

elab :: Source -> I.ThrowC (Notice [SGR]) Elab.Err (L.StateC REPL (Env.Env Elab.Type) (ReaderC Span m)) a -> m a
elab src = runReader (span src) . L.runState env_ . rethrowElabErrors src
