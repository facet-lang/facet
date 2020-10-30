{-# LANGUAGE TypeFamilies #-}
module Facet.REPL
( repl
, kernel
) where

import           Control.Applicative ((<|>))
import           Control.Carrier.Empty.Church
import           Control.Carrier.Error.Church
import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Effect.Lens (use, uses, (%=))
import           Control.Exception (handle)
import           Control.Lens (Lens', lens)
import           Control.Monad (unless, (<=<))
import           Control.Monad.IO.Class
import           Data.Char
import           Data.Colour.RGBSpace.HSL (hsl)
import           Data.Foldable (toList)
import qualified Data.Map as Map
import           Data.Semigroup (stimes)
import qualified Data.Set as Set
import qualified Data.Text as TS
import           Facet.Carrier.Parser.Church hiding (Input)
import           Facet.Carrier.Readline.Haskeline
import qualified Facet.Carrier.Throw.Inject as I
import           Facet.Carrier.Trace.REPL
import           Facet.Core
import           Facet.Driver
import qualified Facet.Elab as Elab
import           Facet.Eval
import           Facet.Flag
import           Facet.Graph
import           Facet.Lens
import           Facet.Name hiding (Meta)
import qualified Facet.Notice as Notice
import           Facet.Notice.Elab
import           Facet.Notice.Parser
import           Facet.Parser as Parser
import           Facet.Pretty
import           Facet.Print as Print hiding (Comp, Type)
import           Facet.REPL.Parser
import           Facet.Source (Source(..), sourceFromString)
import           Facet.Span (Span)
import           Facet.Stack
import           Facet.Style as Style
import qualified Facet.Surface as S
import           Facet.Syntax
import           Prelude hiding (span, unlines)
import           Silkscreen as S hiding (Ann, line)
import           System.Console.ANSI
import           System.Directory
import           System.Exit
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


loop :: (Has Empty sig m, Has Input sig m, Has Output sig m, Has (State REPL) sig m, Has Trace sig m, MonadIO m) => m ()
loop = do
  -- FIXME: handle interrupts
  resp <- prompt
  runError (outputDocLn . prettyNotice) pure $ case resp of
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
  , command ["reload", "r"]     "reload the loaded modules"          Nothing        $ pure (Action (zoom target_ . reloadModules))
  , command ["type", "t"]       "show the type of <expr>"            (Just "expr")
    $ showType <$> runFacet [] expr
  , command ["kind", "k"]       "show the kind of <type>"            (Just "type")
    $ showType <$> runFacet [] Parser.type'
  ]

path' :: TokenParsing p => p FilePath
path' = stringLiteral <|> some (satisfy (not . isSpace))


runAction :: (Has Empty sig m, Has (Error (Notice.Notice Style)) sig m, Has Output sig m, Has (State REPL) sig m, Has Trace sig m, MonadIO m) => Source -> Action -> m ()
runAction src (Action f) = f src

newtype Action = Action (forall sig m . (Has Empty sig m, Has (Error (Notice.Notice Style)) sig m, Has Output sig m, Has (State REPL) sig m, Has Trace sig m, MonadIO m) => Source -> m ())


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
  target_ `zoom` reloadModules src

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


helpDoc :: Doc Style
helpDoc = tabulate2 (stimes (3 :: Int) space) (map entry (getCommands commands))
  where
  entry c =
    ( concatWith (surround (comma <> space)) (map (annotate Style.Command . pretty . (':':)) (symbols c)) <> maybe mempty ((space <>) . enclose (pretty '<') (pretty '>') . pretty) (meta c)
    , w (usage c))
  w = align . fillSep . map pretty . words


prompt :: (Has Input sig m, Has (State REPL) sig m, MonadIO m) => m (Maybe Source)
prompt = do
  line <- gets line
  line_ %= (+ 1)
  fn <- gets promptFunction
  p <- liftIO $ fn line
  fmap (sourceFromString Nothing line) <$> getInputLine p

elab :: Has (State REPL) sig m => Source -> I.ThrowC (Notice.Notice Style) Elab.Err (ReaderC Module (ReaderC Graph (ReaderC Span m))) a -> m a
elab src m = do
  graph <- use (target_.modules_)
  localDefs <- use localDefs_
  runReader (span src) . runReader graph . runReader localDefs . rethrowElabErrors src $ m
