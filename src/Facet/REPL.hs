{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
module Facet.REPL
( repl
) where

import           Control.Algebra
import           Control.Applicative ((<|>))
import           Control.Carrier.Empty.Church
import           Control.Carrier.Error.Church
import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Effect.Lens (use, uses, (%=))
import           Control.Exception (handle)
import           Control.Lens (Lens', lens, (&), (.~))
import           Control.Monad (unless)
import           Control.Monad.IO.Class
import           Data.Char
import           Data.Colour.RGBSpace.HSL (hsl)
import           Data.Foldable (toList)
import qualified Data.Map as Map
import           Data.Semigroup (stimes)
import qualified Data.Set as Set
import           Data.Text (Text)
import           Facet.Carrier.Parser.Church hiding (Input)
import           Facet.Carrier.Readline.Haskeline
import qualified Facet.Carrier.Throw.Inject as I
import           Facet.Carrier.Trace.Output
import           Facet.Carrier.Write.General
import qualified Facet.Carrier.Write.Inject as I
import           Facet.Core.Module
import           Facet.Core.Term hiding (eval)
import           Facet.Core.Type as T hiding (eval, showType)
import           Facet.Driver
import qualified Facet.Elab as Elab
import qualified Facet.Elab.Term as Elab
import           Facet.Eval
import           Facet.Flag
import           Facet.Graph
import           Facet.Lens
import           Facet.Name as Name
import qualified Facet.Notice as Notice
import           Facet.Notice.Elab
import           Facet.Notice.Parser
import           Facet.Parser as Parser
import           Facet.Pretty
import           Facet.Print as Print hiding (meta)
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

repl :: [FilePath] -> IO ExitCode
repl searchPaths
  = handle @IOError (\ e -> ExitFailure 1 <$ print e)
  . fmap (const ExitSuccess)
  . runReadlineWithHistory
  . evalState (defaultREPLState & target_.searchPaths_ .~ Set.fromList searchPaths)
  . evalEmpty
  -- FIXME: move this (and any other flags) into the driver
  . runTrace Nil (toFlag LogTraces False)
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
  , target = defaultTarget
  }
  where
  localDefs = Module (fromList []) [] [] mempty

defaultPromptFunction :: Int -> IO String
defaultPromptFunction _ = pure $ setTitleCode "facet" <> "\STX" <> cyan <> "λ " <> plain
  where
  cyan = setSGRCode [setRGB (hsl 180 1 0.5)] <> "\STX"
  plain = setSGRCode [] <> "\STX"


loop :: (Has (Empty :+: Input :+: Output :+: State (Flag LogTraces) :+: State REPL :+: Trace) sig m, MonadIO m) => m ()
loop = do
  -- FIXME: handle interrupts
  resp <- prompt
  runWrite (outputDocLn . prettyNotice) . runError (outputDocLn . prettyNotice) pure $ case resp of
    Just src -> do
      graph <- use (target_.modules_)
      targets <- use (target_.targets_)
      let ops = foldMap (\ name -> lookupM name graph >>= map (\ (op, assoc) -> (name, op, assoc)) . operators . snd) (toList targets)
      action <- rethrowParseErrors @Style (runParserWithSource src (runFacet (map makeOperator ops) commandParser))
      runReader src $ runAction action
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
  [ command ["help", "h", "?"]  "display this list of commands"      Nothing        $ pure (Action (outputDocLn helpDoc))
  , command ["quit", "q"]       "exit the repl"                      Nothing        $ pure (Action empty)
  , command ["show"]            "show compiler state"                (Just "field") $ choice
    [ showPaths   <$ symbol "paths"
    , showModules <$ symbol "modules"
    , showTargets <$ symbol "targets"
    ]
  , command ["add"]             "add a module/path to the repl"      (Just "item")  $ choice
    [ addPath   <$ symbol "path"   <*> path'
    , addTarget <$ symbol "target" <*> some mname
    ]
  , command ["remove", "rm"]    "remove a module/path from the repl" (Just "item")  $ choice
    [ removePath   <$ symbol "path"   <*> path'
    , removeTarget <$ symbol "target" <*> some mname
    ]
  , command ["reload", "r"]     "reload the loaded modules"          Nothing        $ pure (Action (target_ `zoom` reloadModules))
  , command ["set"]             "set a flag"                         (Just "flag")
    $ setLogTraces <$> choice [ False <$ symbol "no-log-traces", True <$ symbol "log-traces" ]
  , command ["type", "t"]       "show the type of <expr>"            (Just "expr")
    $ showType <$> runFacet [] expr
  -- , command ["kind", "k"]       "show the kind of <type>"            (Just "type")
  --   $ showType <$> runFacet [] Parser.type'
  ]

path' :: TokenParsing p => p FilePath
path' = stringLiteral <|> some (satisfy (not . isSpace))


newtype Action = Action { runAction :: forall sig m . (Has (Empty :+: Error (Notice.Notice (Doc Style)) :+: Output :+: Reader Source :+: State (Flag LogTraces) :+: State REPL :+: Trace :+: I.Write (Notice.Notice (Doc Style))) sig m, MonadIO m) => m () }


showPaths, showModules, showTargets :: Action

showPaths   = Action $ do
  dir <- liftIO getCurrentDirectory
  outputDocLn $ nest 2 $ reflow "current working directory:" </> pretty dir
  searchPaths <- uses (target_.searchPaths_) toList
  unless (null searchPaths)
    $ outputDocLn $ nest 2 $ pretty ("search paths:" :: Text) <\> unlines (map pretty searchPaths)

showModules = Action $ uses (target_.modules_) (unlines . map (\ (name, (path, _)) -> prettyMName name <> maybe mempty ((space <>) . S.parens . pretty) path) . Map.toList . getGraph) >>= outputDocLn

showTargets = Action $ uses (target_.targets_) (unlines . map prettyMName . toList) >>= outputDocLn


addPath, removePath :: FilePath -> Action

addPath path = Action $ target_.searchPaths_ %= Set.insert path

removePath path = Action $ target_.searchPaths_ %= Set.delete path


addTarget, removeTarget :: [MName] -> Action

addTarget targets = Action $ do
  target_.targets_ %= Set.union (Set.fromList targets)
  target_ `zoom` reloadModules

-- FIXME: remove things depending on it
removeTarget targets = Action $ target_.targets_ %= (Set.\\ Set.fromList targets)


setLogTraces :: Bool -> Action
setLogTraces b = Action $ put (toFlag LogTraces b)


showType, showEval :: S.Ann S.Expr -> Action

showType e = Action $ do
  e ::: _T <- runElab $ Elab.elabSynth (Elab.synth (Elab.synthExpr e))
  outputDocLn (getPrint (ann (printValue Nil e ::: printType Nil _T)))

showEval e = Action $ do
  e' ::: _T <- runElab $ Elab.elabSynth $ locally Elab.sig_ (T.global (["Effect", "Console"]:.:U "Output"):) $ Elab.synth (Elab.synthExpr e)
  e'' <- runElab $ runEvalMain (eval e')
  outputDocLn (getPrint (ann (printValue Nil e'' ::: printType Nil _T)))

runEvalMain :: Has Output sig m => Eval m a -> m a
runEvalMain = runEval handle pure
  where
  handle (q :$ ts :$ sp) k = case q of
    FromList ["Effect", "Console"] :.: U "write"
      | FromList [VString s] <- sp -> outputText s *> k unit
    _                              -> k (VOp (q :$ ts :$ sp))
  unit = VCon (["Data", "Unit"] :.: U "unit" :$ Nil :$ Nil)


helpDoc :: Doc Style
helpDoc = tabulate2 (stimes (3 :: Int) space) (map entry (getCommands commands))
  where
  entry c =
    ( concatWith (surround (comma <> space)) (map (annotate Style.Command . pretty . (':':)) (symbols c)) <> maybe mempty ((space <>) . enclose (pretty '<') (pretty '>') . pretty) (meta c)
    , w (usage c))
  w = align . fillSep . map pretty . words


prompt :: (Has (Input :+: State REPL) sig m, MonadIO m) => m (Maybe Source)
prompt = do
  line <- gets line
  line_ %= (+ 1)
  fn <- gets promptFunction
  p <- liftIO $ fn line
  fmap (sourceFromString Nothing line) <$> getInputLine p

runElab :: Has (Reader Source :+: State REPL) sig m => I.WriteC (Notice.Notice (Doc Style)) Elab.Warn (I.ThrowC (Notice.Notice (Doc Style)) Elab.Err (ReaderC MName (ReaderC Module (ReaderC Graph (ReaderC Span m))))) a -> m a
runElab m = do
  graph <- use (target_.modules_)
  localDefs <- use localDefs_
  src <- ask
  runReader (span src) . runReader graph . runReader localDefs . runReader ((name :: Module -> MName) localDefs) . rethrowElabErrors src . rethrowElabWarnings src $ m
