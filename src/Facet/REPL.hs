{-# LANGUAGE TypeFamilies #-}
module Facet.REPL
( repl
) where

import           Control.Applicative ((<|>))
import           Control.Carrier.Empty.Church
import           Control.Carrier.Error.Church
import           Control.Carrier.Fresh.Church
import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Effect.Lens (use, uses, (%=), (.=))
import           Control.Lens (Getting, Lens', at, lens)
import           Control.Monad (unless, void)
import           Control.Monad.IO.Class
import           Data.Char
import           Data.Colour.RGBSpace.HSL (hsl)
import           Data.Foldable (toList)
import qualified Data.Map as Map
import           Data.Maybe (catMaybes)
import           Data.Semigroup (stimes)
import qualified Data.Set as Set
import qualified Data.Text as TS
import           Data.Text.Lazy (unpack)
import           Data.Traversable (for)
import           Facet.Algebra hiding (Algebra)
import           Facet.Carrier.Parser.Church
import           Facet.Carrier.Readline.Haskeline
import qualified Facet.Carrier.Throw.Inject as I
import           Facet.Core
import qualified Facet.Elab as Elab
import           Facet.Eval
import           Facet.Graph
import           Facet.Name hiding (Meta, use)
import qualified Facet.Notice as Notice
import           Facet.Notice.Elab
import           Facet.Notice.Parser
import           Facet.Parser
import           Facet.Pretty
import           Facet.Print as Print hiding (Type)
import           Facet.REPL.Parser
import           Facet.Source (Source(..), readSourceFromFile, sourceFromString)
import           Facet.Span (Span)
import           Facet.Stack
import           Facet.Style as Style
import qualified Facet.Surface as S
import           Facet.Syntax
import           Prelude hiding (print, span, unlines)
import qualified Prettyprinter as P
import           Silkscreen as S hiding (Ann, line)
import           System.Console.ANSI
import           System.Directory
import qualified System.FilePath as FP
import           System.IO.Error
import           Text.Parser.Char hiding (space)
import           Text.Parser.Combinators
import           Text.Parser.Token hiding (brackets, comma)

repl :: IO ()
repl
  = runReadlineWithHistory
  . evalState defaultREPLState
  . evalEmpty
  $ loop


data REPL = REPL
  { line           :: Int
  , promptFunction :: Int -> IO String
  , localDefs      :: Module -- ^ The module where definitions made in the REPL live. Not a part of modules.
  , modules        :: Graph
  , targets        :: Set.Set MName
  -- FIXME: break this down by file/module/whatever so we can load multiple packages
  , searchPaths    :: Set.Set FilePath
  }

line_ :: Lens' REPL Int
line_ = lens line (\ r line -> r{ line })

localDefs_ :: Lens' REPL Module
localDefs_ = lens localDefs (\ r localDefs -> r{ localDefs })

modules_ :: Lens' REPL Graph
modules_ = lens modules (\ r modules -> r{ modules })

targets_ :: Lens' REPL (Set.Set MName)
targets_ = lens targets (\ r targets -> r{ targets })

searchPaths_ :: Lens' REPL (Set.Set FilePath)
searchPaths_ = lens searchPaths (\ r searchPaths -> r{ searchPaths })

defaultREPLState :: REPL
defaultREPLState = REPL
  { line           = 0
  , promptFunction = defaultPromptFunction
  , localDefs
  , modules
  , targets        = mempty
  , searchPaths    = Set.singleton "src"
  }
  where
  localDefs = Module (MName mempty) [] []
  modules = singleton Nothing kernel

defaultPromptFunction :: Int -> IO String
defaultPromptFunction _ = pure $ setTitleCode "facet" <> cyan <> "λ " <> plain
  where
  cyan = setSGRCode [setRGB (hsl 180 1 0.5)]
  plain = setSGRCode []


kernel :: Module
kernel = Module kernelName []
  [ (T (UName (TS.pack "Type")), Just (DTerm VType) ::: VType)
  ]
  where
  kernelName = MName (TS.pack "Kernel")


loop :: (Has Empty sig m, Has Readline sig m, Has (State REPL) sig m, MonadIO m) => m ()
loop = do
  resp <- prompt
  runError (print . prettyNotice') pure $ case resp of
    Just src -> rethrowParseErrors @Style (runParserWithSource src commandParser) >>= runAction src
    Nothing  -> pure ()
  loop
  where
  commandParser = runFacet [] [] (whole (parseCommands commands <|> Eval <$> expr))

runAction :: (Has Empty sig m, Has (Error (Notice.Notice Style)) sig m, Has Readline sig m, Has (State REPL) sig m, MonadIO m) => Source -> Action -> m ()
runAction src = \case
  Help -> print helpDoc
  Quit -> empty
  Show t -> case t of
    ShowPaths   -> do
      dir <- liftIO getCurrentDirectory
      print $ nest 2 $ reflow "current working directory:" </> pretty dir
      searchPaths <- gets (toList . searchPaths)
      unless (null searchPaths)
        $ print $ nest 2 $ pretty "search paths:" <\> unlines (map pretty searchPaths)
    ShowModules -> uses modules_ (unlines . map (\ (name, (path, _)) -> pretty name <> maybe mempty ((space <>) . S.parens . pretty) path) . Map.toList . getGraph) >>= print
    ShowTargets -> uses targets_ (unlines . map pretty . toList) >>= print
  Add (ModPath path) -> searchPaths_ %= Set.insert path
  Add (ModTarget targets) -> do
    targets_ %= Set.union (Set.fromList targets)
    void $ reload src
  Remove (ModPath path) -> searchPaths_ %= Set.delete path
  -- FIXME: remove things depending on it
  Remove (ModTarget targets) -> targets_ %= (Set.\\ Set.fromList targets)
  Reload -> void $ reload src
  Type e -> do
    _ ::: _T <- elab src $ Elab.elabWith (\ s (e ::: _T) -> (:::) <$> Elab.apply s e <*> Elab.apply s _T) (Elab.elabExpr e Nothing)
    print (prettyCode (ann (foldSExpr surface Nil e ::: foldCValue surface Nil (generalize _T))))
  Eval e -> do
    e' ::: _T <- elab src $ Elab.elabWith (\ s (e ::: _T) -> (:::) <$> Elab.apply s e <*> Elab.apply s _T) (Elab.elabExpr e Nothing)
    e'' <- elab src $ eval e'
    print (prettyCode (ann (foldCValue surface Nil e'' ::: foldCValue surface Nil _T)))


-- TODO:
-- - multiline
-- - breakpoints
commands :: Commands Action
commands = choice
  [ command ["help", "h", "?"]  "display this list of commands"      Nothing        $ pure Help
  , command ["quit", "q"]       "exit the repl"                      Nothing        $ pure Quit
  , command ["show"]            "show compiler state"                (Just "field") $ Show <$> choice
    [ ShowPaths   <$ token (string "paths")
    , ShowModules <$ token (string "modules")
    , ShowTargets <$ token (string "targets")
    ]
  , command ["add"]             "add a module/path to the repl"      (Just "item")  $ choice
    [ Add . ModPath   <$ token (string "path")   <*> path'
    , Add . ModTarget <$ token (string "target") <*> some mname
    ]
  , command ["remove", "rm"]    "remove a module/path from the repl" (Just "item")  $ choice
    [ Remove . ModPath   <$ token (string "path")   <*> path'
    , Remove . ModTarget <$ token (string "target") <*> some mname
    ]
  , command ["reload", "r"]     "reload the loaded modules"          Nothing        $ pure Reload
  , command ["type", "t"]       "show the type of <expr>"            (Just "expr")
    $ Type <$> runFacet [] [] expr
  , command ["kind", "k"]       "show the kind of <type>"            (Just "type")
    $ Type <$> runFacet [] [] type'
  ]

path' :: TokenParsing p => p FilePath
path' = stringLiteral <|> some (satisfy (not . isSpace))


-- FIXME: either remove this in favour of shoving the interpretations into the Commands directly, or else figure out a pleasant way to derive the Commands from it.
data Action
  = Help
  | Quit
  | Show ShowField
  | Add ModField
  | Remove ModField
  | Reload
  | Type (S.Ann S.Expr)
  | Eval (S.Ann S.Expr)

data ShowField
  = ShowPaths
  | ShowModules
  | ShowTargets

data ModField
  = ModPath FilePath
  | ModTarget [MName]


reload :: (Has (Error (Notice.Notice Style)) sig m, Has Readline sig m, Has (State REPL) sig m, MonadIO m) => Source -> m [Maybe Module]
reload src = do
  modules <- targets_ ~> \ targets -> do
    -- FIXME: remove stale modules
    targetHeads <- traverse (loadModuleHeader src) (toList targets)
    rethrowGraphErrors src $ loadOrder (fmap toNode . loadModuleHeader src) (map toNode targetHeads)
  let nModules = length modules
  results <- evalFresh 1 $ for modules $ \ (name, path, src) -> do
    i <- fresh
    print $ annotate Progress (brackets (ratio i nModules)) <+> nest 2 (group (fillSep [ pretty "Loading", pretty name ]))

    -- FIXME: skip gracefully (maybe print a message) if any of its imports are unavailable due to earlier errors
    (Just <$> loadModule name path src) `catchError` \ err -> Nothing <$ print (prettyNotice' err)
  let nSuccess = length (catMaybes results)
  print . fillSep $ if nModules == nSuccess then
      [ annotate Success (pretty Notice.Info)  <> S.colon, annotate Success (pretty nModules),         reflow "modules loaded." ]
    else
      [ annotate Failure (pretty Notice.Error) <> S.colon, annotate Failure (ratio nSuccess nModules), reflow "modules loaded." ]
  pure results
  where
  ratio n d = pretty n <+> pretty "of" <+> pretty d
  toNode (n, path, source, imports) = Node n (map ((S.name :: S.Import -> MName) . S.out) imports) (n, path, source)

loadModuleHeader :: (Has (State REPL) sig m, Has (Throw (Notice.Notice Style)) sig m, MonadIO m) => Source -> MName -> m (MName, FilePath, Source, [S.Ann S.Import])
loadModuleHeader src name = do
  path <- resolveName name
  src <- rethrowIOErrors src $ readSourceFromFile path
  -- FIXME: validate that the name matches
  (name', is) <- rethrowParseErrors @Style (runParserWithSource src (runFacet [] [] moduleHeader))
  pure (name', path, src, is)

loadModule :: (Has (State REPL) sig m, Has (Throw (Notice.Notice Style)) sig m) => MName -> FilePath -> Source -> m Module
loadModule name path src = do
  m <- rethrowParseErrors @Style (runParserWithSource src (runFacet [] [] (whole module')))
  graph <- use modules_
  m <- rethrowElabErrors src Code . runReader graph $ Elab.elabModule m
  modules_.at name .= Just (Just path, m)
  pure m

resolveName :: (Has (State REPL) sig m, MonadIO m) => MName -> m FilePath
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

print :: (Has Readline sig m, MonadIO m) => Doc Style -> m ()
print d = do
  opts <- liftIO layoutOptionsForTerminal
  outputStrLn (unpack (renderLazy (P.reAnnotateS terminalStyle (layoutSmart opts d))))

prettyNotice' :: Notice.Notice Style -> Doc Style
prettyNotice' = P.reAnnotate Style.Notice . Notice.prettyNotice

prettyCode :: Print -> Doc Style
prettyCode = P.reAnnotate Code . getPrint

elab :: Has (State REPL) sig m => Source -> I.ThrowC (Notice.Notice Style) Elab.Err (ReaderC Module (ReaderC Graph (ReaderC Span m))) a -> m a
elab src m = do
  graph <- use modules_
  localDefs <- use localDefs_
  runReader (span src) . runReader graph . runReader localDefs . rethrowElabErrors src Code $ m


-- | Compose a getter onto the input of a Kleisli arrow and run it on the 'State'.
(~>) :: Has (State s) sig m => Getting a s a -> (a -> m b) -> m b
lens ~> act = use lens >>= act

infixr 2 ~>


rethrowIOErrors :: (Has (Throw (Notice.Notice Style)) sig m, MonadIO m) => Source -> IO a -> m a
rethrowIOErrors src m = liftIO (tryIOError m) >>= either (throwError . ioErrorToNotice src) pure

rethrowGraphErrors :: Source -> I.ThrowC (Notice.Notice Style) GraphErr m a -> m a
rethrowGraphErrors src = I.runThrow formatGraphErr
  where
  formatGraphErr (CyclicImport path) = Notice.Notice (Just Notice.Error) src (reflow "cyclic import") (map pretty (toList path))

ioErrorToNotice :: Source -> IOError -> Notice.Notice Style
ioErrorToNotice src err = Notice.Notice (Just Notice.Error) src (group (reflow (show err))) []
