{-# LANGUAGE TypeFamilies #-}
module Facet.REPL
( repl
, kernel
) where

import           Control.Applicative ((<|>))
import           Control.Carrier.Empty.Church
import           Control.Carrier.Error.Church
import           Control.Carrier.Fresh.Church
import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Effect.Lens (use, uses, (%=), (.=), (<~))
import           Control.Exception (handle)
import           Control.Lens (Getting, Lens', at, lens)
import           Control.Monad (unless, (<=<))
import           Control.Monad.IO.Class
import           Data.Char
import           Data.Colour.RGBSpace.HSL (hsl)
import           Data.Foldable (toList)
import qualified Data.Map as Map
import           Data.Maybe (catMaybes)
import           Data.Semigroup (stimes)
import qualified Data.Set as Set
import qualified Data.Text as TS
import           Data.Traversable (for)
import           Facet.Carrier.Parser.Church
import           Facet.Carrier.Readline.Haskeline
import qualified Facet.Carrier.Throw.Inject as I
import           Facet.Carrier.Trace.REPL
import           Facet.Core
import           Facet.Driver
import qualified Facet.Elab as Elab
import           Facet.Eval
import           Facet.Flag
import           Facet.Graph
import           Facet.Name hiding (Meta)
import qualified Facet.Notice as Notice
import           Facet.Notice.Elab
import           Facet.Notice.Parser
import           Facet.Parser as Parser
import           Facet.Pretty
import           Facet.Print as Print hiding (Comp, Type)
import           Facet.REPL.Parser
import           Facet.Source (Source(..), readSourceFromFile, sourceFromString)
import           Facet.Span (Span)
import           Facet.Stack
import           Facet.Style as Style
import qualified Facet.Surface as S
import           Facet.Syntax
import           Prelude hiding (span, unlines)
import qualified Prettyprinter as P
import           Silkscreen as S hiding (Ann, line)
import           System.Console.ANSI
import           System.Directory
import           System.Exit
import qualified System.FilePath as FP
import           System.IO.Error
import           Text.Parser.Char hiding (space)
import           Text.Parser.Combinators
import           Text.Parser.Token hiding (brackets, comma)

repl :: IO ExitCode
repl
  = handle @IOError (\ e -> ExitFailure 1 <$ print e)
  . fmap (const ExitSuccess)
  . runReadlineWithHistory
  . evalState defaultREPLState
  . evalEmpty
  . evalState (toFlag LogTraces False)
  . runTrace Nil
  $ loop


data REPL = REPL
  { line           :: Int
  , promptFunction :: Int -> IO String
  , localDefs      :: Module -- ^ The module where definitions made in the REPL live. Not a part of modules.
  -- FIXME: generalize this to support multiple targets.
  , target         :: Target
  }

line_ :: Lens' REPL Int
line_ = lens line (\ r line -> r{ line })

localDefs_ :: Lens' REPL Module
localDefs_ = lens localDefs (\ r localDefs -> r{ localDefs })

target_ :: Lens' REPL Target
target_ = lens target (\ r target -> r{ target })

defaultREPLState :: REPL
defaultREPLState = REPL
  { line           = 0
  , promptFunction = defaultPromptFunction
  , localDefs
  , target = Target
    { modules
    , targets        = mempty
    , searchPaths    = Set.singleton "lib"
    }
  }
  where
  localDefs = Module (MName mempty) [] [] mempty
  modules = singleton Nothing kernel

defaultPromptFunction :: Int -> IO String
defaultPromptFunction _ = pure $ setTitleCode "facet" <> "\STX" <> cyan <> "λ " <> plain
  where
  cyan = setSGRCode [setRGB (hsl 180 1 0.5)] <> "\STX"
  plain = setSGRCode [] <> "\STX"


kernel :: Module
kernel = Module kernelName [] [] $ Map.fromList
  [ (typeName, Decl (Just (DTerm VType)) (Comp mempty VType))
  ]
  where
  typeName = T (UName (TS.pack "Type"))
  kernelName = MName (TS.pack "Kernel")


loop :: (Has Empty sig m, Has Readline sig m, Has (State REPL) sig m, Has Trace sig m, MonadIO m) => m ()
loop = do
  -- FIXME: handle interrupts
  resp <- prompt
  runError (outputDocLn . prettyNotice') pure $ case resp of
    Just src -> do
      graph <- use (target_.modules_)
      targets <- use (target_.targets_)
      let ops = foldMap (operators . snd <=< (`lookupM` graph)) (toList targets)
      action <- rethrowParseErrors @Style (runParserWithSource src (runFacet (map makeOperator ops) commandParser))
      runAction src action
    Nothing  -> pure ()
  loop
  where
  commandParser = whole (parseCommands commands <|> showEval <$> expr)


-- TODO:
-- - multiline
-- - breakpoints
-- - shell commands
commands :: Commands Action
commands = choice
  [ command ["help", "h", "?"]  "display this list of commands"      Nothing        $ pure (Action (const (outputDocLn helpDoc)))
  , command ["quit", "q"]       "exit the repl"                      Nothing        $ pure (Action (const empty))
  , command ["show"]            "show compiler state"                (Just "field") $ choice
    [ showPaths   <$ token (string "paths")
    , showModules <$ token (string "modules")
    , showTargets <$ token (string "targets")
    ]
  , command ["add"]             "add a module/path to the repl"      (Just "item")  $ choice
    [ addPath   <$ token (string "path")   <*> path'
    , addTarget <$ token (string "target") <*> some mname
    ]
  , command ["remove", "rm"]    "remove a module/path from the repl" (Just "item")  $ choice
    [ removePath   <$ token (string "path")   <*> path'
    , removeTarget <$ token (string "target") <*> some mname
    ]
  , command ["reload", "r"]     "reload the loaded modules"          Nothing        $ pure (Action reload)
  , command ["type", "t"]       "show the type of <expr>"            (Just "expr")
    $ showType <$> runFacet [] expr
  , command ["kind", "k"]       "show the kind of <type>"            (Just "type")
    $ showType <$> runFacet [] Parser.type'
  ]

path' :: TokenParsing p => p FilePath
path' = stringLiteral <|> some (satisfy (not . isSpace))


runAction :: (Has Empty sig m, Has (Error (Notice.Notice Style)) sig m, Has Readline sig m, Has (State REPL) sig m, Has Trace sig m, MonadIO m) => Source -> Action -> m ()
runAction src (Action f) = f src

newtype Action = Action (forall sig m . (Has Empty sig m, Has (Error (Notice.Notice Style)) sig m, Has Readline sig m, Has (State REPL) sig m, Has Trace sig m, MonadIO m) => Source -> m ())


showPaths, showModules, showTargets :: Action

showPaths   = Action $ \ _ -> do
  dir <- liftIO getCurrentDirectory
  outputDocLn $ nest 2 $ reflow "current working directory:" </> pretty dir
  searchPaths <- uses (target_.searchPaths_) toList
  unless (null searchPaths)
    $ outputDocLn $ nest 2 $ pretty "search paths:" <\> unlines (map pretty searchPaths)

showModules = Action $ \ _ -> uses (target_.modules_) (unlines . map (\ (name, (path, _)) -> pretty name <> maybe mempty ((space <>) . S.parens . pretty) path) . Map.toList . getGraph) >>= outputDocLn

showTargets = Action $ \ _ -> uses (target_.targets_) (unlines . map pretty . toList) >>= outputDocLn

addPath :: FilePath -> Action
addPath path = Action $ \ _ -> target_.searchPaths_ %= Set.insert path

addTarget :: [MName] -> Action
addTarget targets = Action $ \ src -> do
  target_.targets_ %= Set.union (Set.fromList targets)
  reload src

removePath :: FilePath -> Action
removePath path = Action $ \ _ -> target_.searchPaths_ %= Set.delete path

-- FIXME: remove things depending on it
removeTarget :: [MName] -> Action
removeTarget targets = Action $ \ _ -> target_.targets_ %= (Set.\\ Set.fromList targets)

showType :: S.Ann S.Expr -> Action
showType e = Action $ \ src -> do
  e ::: _T <- elab src $ Elab.elabWith (\ s (e ::: _T) -> pure $ generalize s e ::: generalize s _T) (Elab.synth (Elab.synthExpr e))
  outputDocLn (prettyCode (ann (printValue Nil e ::: printValue Nil _T)))

showEval :: S.Ann S.Expr -> Action
showEval e = Action $ \ src -> do
  e' ::: _T <- elab src $ Elab.elabWith (\ s (e ::: _T) -> pure $ generalize s e ::: generalize s _T) (Elab.synth (Elab.synthExpr e))
  e'' <- elab src $ runEvalMain (eval e')
  outputDocLn (prettyCode (ann (printValue Nil e'' ::: printValue Nil _T)))

-- FIXME: should actually handle “syscall” effects here.
runEvalMain :: Applicative m => Eval m a -> m a
runEvalMain = runEval (fmap runEvalMain . flip ($)) pure


reload :: (Has (Error (Notice.Notice Style)) sig m, Has Readline sig m, Has (State REPL) sig m, Has Trace sig m, MonadIO m) => Source -> m ()
reload src = target_ `zoom` do
  modules <- targets_ ~> \ targets -> do
    -- FIXME: remove stale modules
    -- FIXME: failed module header parses shouldn’t invalidate everything.
    targetHeads <- traverse (loadModuleHeader src . Right) (toList targets)
    rethrowGraphErrors src $ loadOrder (fmap toNode . loadModuleHeader src . Right) (map toNode targetHeads)
  let nModules = length modules
  results <- evalFresh 1 $ for modules $ \ (name, path, src, imports) -> do
    i <- fresh
    outputDocLn $ annotate Progress (brackets (ratio i nModules)) <+> nest 2 (group (fillSep [ pretty "Loading", pretty name ]))

    -- FIXME: skip gracefully (maybe print a message) if any of its imports are unavailable due to earlier errors
    (Just <$> loadModule name path src imports) `catchError` \ err -> Nothing <$ outputDocLn (prettyNotice' err)
  let nSuccess = length (catMaybes results)
      status
        | nModules == nSuccess = annotate Success (pretty nModules)
        | otherwise            = annotate Failure (ratio nSuccess nModules)
  outputDocLn (fillSep [status, reflow "modules loaded."])
  where
  ratio n d = pretty n <+> pretty "of" <+> pretty d
  toNode (n, path, source, imports) = let imports' = map ((S.name :: S.Import -> MName) . S.out) imports in Node n imports' (n, path, source, imports')

loadModuleHeader :: (Has (State Target) sig m, Has (Throw (Notice.Notice Style)) sig m, MonadIO m) => Source -> Either FilePath MName -> m (MName, FilePath, Source, [S.Ann S.Import])
loadModuleHeader src target = do
  path <- case target of
    Left path  -> pure path
    Right name -> resolveName name
  src <- rethrowIOErrors src $ readSourceFromFile path
  -- FIXME: validate that the name matches
  (name', is) <- rethrowParseErrors @Style (runParserWithSource src (runFacet [] (whiteSpace *> moduleHeader)))
  pure (name', path, src, is)

loadModule :: (Has (State Target) sig m, Has (Throw (Notice.Notice Style)) sig m, Has Trace sig m) => MName -> FilePath -> Source -> [MName] -> m Module
loadModule name path src imports = do
  graph <- use modules_
  let ops = foldMap (operators . snd <=< (`lookupM` graph)) imports
  m <- rethrowParseErrors @Style (runParserWithSource src (runFacet (map makeOperator ops) (whole module')))
  m <- rethrowElabErrors src . runReader graph $ Elab.elabModule m
  modules_.at name .= Just (Just path, m)
  pure m

resolveName :: (Has (State Target) sig m, MonadIO m) => MName -> m FilePath
resolveName name = do
  searchPaths <- use searchPaths_
  let namePath = toPath name FP.<.> ".facet"
  path <- liftIO $ findFile (toList searchPaths) namePath
  case path of
    Just path -> pure path
    Nothing   -> liftIO $ ioError $ mkIOError doesNotExistErrorType "loadModule" Nothing (Just namePath)
  where
  toPath (name :. component) = toPath name FP.</> TS.unpack component
  toPath (MName component)   = TS.unpack component


helpDoc :: Doc Style
helpDoc = tabulate2 (stimes (3 :: Int) space) (map entry (getCommands commands))
  where
  entry c =
    ( concatWith (surround (comma <> space)) (map (annotate Style.Command . pretty . (':':)) (symbols c)) <> maybe mempty ((space <>) . enclose (pretty '<') (pretty '>') . pretty) (meta c)
    , w (usage c))
  w = align . fillSep . map pretty . words


prompt :: (Has Readline sig m, Has (State REPL) sig m, MonadIO m) => m (Maybe Source)
prompt = do
  line <- gets line
  line_ %= (+ 1)
  fn <- gets promptFunction
  p <- liftIO $ fn line
  fmap (sourceFromString Nothing line) <$> getInputLine p

prettyNotice' :: Notice.Notice Style -> Doc Style
prettyNotice' = P.reAnnotate Style.Notice . Notice.prettyNotice

prettyCode :: Print -> Doc Style
prettyCode = P.reAnnotate Code . getPrint

elab :: Has (State REPL) sig m => Source -> I.ThrowC (Notice.Notice Style) Elab.Err (ReaderC Module (ReaderC Graph (ReaderC Span m))) a -> m a
elab src m = do
  graph <- use (target_.modules_)
  localDefs <- use localDefs_
  runReader (span src) . runReader graph . runReader localDefs . rethrowElabErrors src $ m


zoom :: Has (State s) sig m => Lens' s a -> StateC a m () -> m ()
zoom lens action = lens <~> (`execState` action)

infixr 2 `zoom`

-- | Compose a getter onto the input of a Kleisli arrow and run it on the 'State'.
(~>) :: Has (State s) sig m => Getting a s a -> (a -> m b) -> m b
lens ~> act = use lens >>= act

infixr 2 ~>

-- | Compose a lens onto either side of a Kleisli arrow and run it on the 'State'.
(<~>) :: Has (State s) sig m => Lens' s a -> (a -> m a) -> m ()
lens <~> act = lens <~ lens ~> act

infixr 2 <~>


rethrowIOErrors :: (Has (Throw (Notice.Notice Style)) sig m, MonadIO m) => Source -> IO a -> m a
rethrowIOErrors src m = liftIO (tryIOError m) >>= either (throwError . ioErrorToNotice src) pure

rethrowGraphErrors :: Source -> I.ThrowC (Notice.Notice Style) GraphErr m a -> m a
rethrowGraphErrors src = I.runThrow formatGraphErr
  where
  formatGraphErr (CyclicImport path) = Notice.Notice (Just Notice.Error) src (reflow "cyclic import") (map pretty (toList path))

ioErrorToNotice :: Source -> IOError -> Notice.Notice Style
ioErrorToNotice src err = Notice.Notice (Just Notice.Error) src (group (reflow (show err))) []
