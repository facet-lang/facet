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
import           Control.Carrier.Fresh.Church
import           Control.Carrier.Reader
import           Control.Carrier.Readline.Haskeline
import           Control.Carrier.State.Church
import           Control.Effect.Lens (use, (%=), (<~))
import           Control.Lens (Getting, Lens', itraverse, lens)
import           Control.Monad.IO.Class
import           Data.Char
import           Data.Colour.RGBSpace.HSL (hsl)
import           Data.Foldable (toList)
import qualified Data.Map as Map
import           Data.Semigroup
import           Data.Text.Lazy (unpack)
import           Facet.Algebra hiding (Algebra)
import           Facet.Carrier.Parser.Church
import qualified Facet.Carrier.State.Lens as L
import qualified Facet.Carrier.Throw.Inject as I
import qualified Facet.Elab as Elab
import qualified Facet.Env as Env
import           Facet.Notice
import           Facet.Notice.Elab
import           Facet.Notice.Parser
import           Facet.Parser
import           Facet.Pretty
import           Facet.Print
import           Facet.REPL.Parser
import           Facet.Source (Source(..), readSourceFromFile, sourceFromString)
import           Facet.Stack
import           Facet.Surface (Expr, Type)
import           Facet.Syntax
import           Prelude hiding (print, span)
import           Silkscreen hiding (line)
import           System.Console.ANSI
import           System.IO.Error
import           Text.Parser.Char hiding (space)
import           Text.Parser.Combinators
import           Text.Parser.Position
import           Text.Parser.Token hiding (brackets, comma)

repl :: IO ()
repl
  = runReadlineWithHistory
  . evalState defaultREPLState
  . evalEmpty
  $ loop


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

defaultREPLState :: REPL
defaultREPLState = REPL
  { line           = 0
  , files          = mempty
  , promptFunction = defaultPromptFunction
  , env            = mempty
  }

defaultPromptFunction :: Int -> IO String
defaultPromptFunction _ = pure $ setTitleCode "facet" <> cyan <> "λ " <> plain
  where
  cyan = setSGRCode [setRGB (hsl 180 1 0.5)]
  plain = setSGRCode []


data File = File
  { loaded :: Bool
  }


loop :: (Has Empty sig m, Has Readline sig m, Has (State REPL) sig m, MonadIO m) => m ()
loop = do
  resp <- prompt
  runError (print . prettyNotice) pure $ case resp of
    -- FIXME: evaluate expressions
    Just src -> rethrowParseErrors (runParserWithSource src commandParser) >>= runAction src
    Nothing  -> pure ()
  loop
  where
  commandParser = runFacet [] (whole (parseCommands commands))

  runAction src = \case
    Help -> print helpDoc
    Quit -> empty
    Load path -> load src path
    Reload -> reload src
    Type e -> do
      _ ::: _T <- elab src $ Elab.elabWith (\ s (e ::: _T) -> (:::) <$> Elab.apply s e <*> Elab.apply s _T) (Elab.elabExpr e Nothing)
      print (getPrint (ann (foldSExpr surface Nil e ::: foldCValue surface Nil _T)))
    Kind t -> do
      _ ::: _T <- elab src $ Elab.elabWith (\ s (t ::: _T) -> (:::) <$> Elab.apply s t <*> Elab.apply s _T) (Elab.elabType t Nothing)
      print (getPrint (ann (foldSType surface Nil t ::: foldCValue surface Nil _T)))
    Eval e -> do -- FIXME: actually evaluate
      _ ::: _T <- elab src $ Elab.elabWith (\ s (e ::: _T) -> (:::) <$> Elab.apply s e <*> Elab.apply s _T) (Elab.elabExpr e Nothing)
      print (getPrint (ann (foldSExpr surface Nil e ::: foldCValue surface Nil _T)))


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

type_ = Type <$> runFacet [] (whole expr)
kind_ = Kind <$> runFacet [] (whole type')


data Action
  = Help
  | Quit
  | Load FilePath
  | Reload
  | Type (Spanned Expr)
  | Kind (Spanned Type)
  | Eval (Spanned Expr)

load :: (Has (Error (Notice [SGR])) sig m, Has Readline sig m, Has (State REPL) sig m, MonadIO m) => Source -> FilePath -> m ()
load src path = do
  files_ %= Map.insert path File{ loaded = False }
  reload src

reload :: (Has (Error (Notice [SGR])) sig m, Has Readline sig m, Has (State REPL) sig m, MonadIO m) => Source -> m ()
reload src = do
  -- FIXME: order with a topological sort on imports, once those exist
  evalFresh 1 $ files_ <~> \ files -> itraverse (reloadFile (length files)) files
  files <- use files_
  let lnAll = length files
      lnLoaded = length (filter loaded (toList files))
      style = if lnLoaded == lnAll then success else failure
  print $ fillSep [annotate style (fillSep [pretty lnLoaded, pretty "of", pretty lnAll]), plural (pretty "file") (pretty "files") lnLoaded, pretty "loaded."]
  where
  -- FIXME: check whether files need reloading
  reloadFile ln path file = if loaded file then pure file else do
    i <- fresh
    -- FIXME: print the module name
    print $ annotate info (brackets (pretty i <+> pretty "of" <+> pretty ln)) <+> nest 2 (group (fillSep [ pretty "Loading", pretty path ]))

    (do
      src <- liftIO ((Right <$> readSourceFromFile path) `catchIOError` (pure . Left . ioErrorToNotice src)) >>= either throwError pure
      m <- rethrowParseErrors (runParserWithSource src (runFacet [] (whole module')))
      (env, m') <- elab src $ Elab.elabModule m
      env_ %= (<> env)
      file{ loaded = True } <$ print (getPrint (foldCModule surface m')))
      `catchError` \ n ->
        file <$ print (indent 2 (prettyNotice n))

failure :: [SGR]
failure = [setRGB (hsl 0 1 0.5), setBold]

success :: [SGR]
success = [setRGB (hsl 120 1 0.5), setBold]

info :: [SGR]
info = [setRGB (hsl 0 0 0.5), setBold]

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


-- | Compose a getter onto the input of a Kleisli arrow and run it on the 'State'.
(~>) :: Has (State s) sig m => Getting a s a -> (a -> m b) -> m b
lens ~> act = use lens >>= act

infixr 2 ~>

-- | Compose a lens onto either side of a Kleisli arrow and run it on the 'State'.
(<~>) :: Has (State s) sig m => Lens' s a -> (a -> m a) -> m ()
lens <~> act = lens <~ lens ~> act

infixr 2 <~>


ioErrorToNotice :: Source -> IOError -> Notice [SGR]
ioErrorToNotice src err = Notice (Just Error) src (group (reflow (show err))) []
