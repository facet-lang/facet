-- | Operations driving the loading and processing of modules.
module Facet.Driver
( Target(..)
, modules_
, targets_
, searchPaths_
, defaultTarget
, kernel
  -- * Module loading
, reloadModules
, ModuleHeader(..)
, loadModuleHeader
, loadModule
, resolveName
  -- * Errors
, rethrowIOErrors
, rethrowGraphErrors
) where

import           Control.Algebra
import           Control.Carrier.Fresh.Church
import           Control.Carrier.Reader
import           Control.Effect.Error
import           Control.Effect.Lens (use, uses, (.=))
import           Control.Effect.State
import           Control.Lens (Lens', at, lens)
import           Control.Monad.IO.Class
import           Data.Foldable (toList)
import           Data.Maybe (catMaybes)
import qualified Data.Set as Set
import qualified Data.Text as TS
import           Data.Traversable (for)
import           Facet.Carrier.Parser.Church
import qualified Facet.Carrier.Throw.Inject as I
import           Facet.Core.Module
import           Facet.Effect.Readline
import           Facet.Effect.Write
import qualified Facet.Elab.Term as Elab
import           Facet.Graph
import           Facet.Lens
import           Facet.Name
import qualified Facet.Notice as Notice
import           Facet.Notice.Elab (rethrowElabErrors, rethrowElabWarnings)
import           Facet.Notice.Parser (rethrowParseErrors)
import           Facet.Parser
import           Facet.Pretty
import           Facet.Print (Options)
import           Facet.Snoc
import           Facet.Source
import           Facet.Style
import qualified Facet.Surface as Import (Import(..))
import qualified Facet.Surface as S
import           Silkscreen
import           System.Directory (findFile)
import qualified System.FilePath as FP
import           System.IO.Error
import           Text.Parser.Token (whiteSpace)

data Target = Target
  { modules     :: Graph
  , targets     :: Set.Set MName
  , searchPaths :: Set.Set FilePath
  }

modules_ :: Lens' Target Graph
modules_ = lens modules (\ r modules -> r{ modules })

targets_ :: Lens' Target (Set.Set MName)
targets_ = lens targets (\ r targets -> r{ targets })

searchPaths_ :: Lens' Target (Set.Set FilePath)
searchPaths_ = lens searchPaths (\ r searchPaths -> r{ searchPaths })

defaultTarget :: Target
defaultTarget = Target
  { modules = singleton Nothing kernel
  , targets = mempty
  , searchPaths = mempty
  }


kernel :: Module
kernel = Module kernelName [] [] $ Scope mempty
  -- FIXME: include things like Type and Interface
  where
  kernelName = fromList [TS.pack "Kernel"]


-- Module loading

reloadModules :: (Has (Error (Notice.Notice (Doc Style)) :+: Output :+: State Options :+: State Target :+: Write (Notice.Notice (Doc Style))) sig m, MonadIO m) => m ()
reloadModules = do
  searchPaths <- uses searchPaths_ toList
  modules <- targets_ ~> \ targets -> do
    -- FIXME: remove stale modules
    -- FIXME: failed module header parses shouldn’t invalidate everything.
    targetHeads <- traverse (loadModuleHeader searchPaths . Right) (toList targets)
    rethrowGraphErrors [] $ loadOrder (fmap toNode . loadModuleHeader searchPaths . Right) (map toNode targetHeads)
  let nModules = length modules
  results <- evalFresh 1 $ for modules $ \ (ModuleHeader name path src imports) -> do
    i <- fresh
    outputDocLn $ annotate Progress (brackets (ratio i nModules)) <+> nest 2 (group (fillSep [ pretty "Loading", prettyMName name ]))

    -- FIXME: skip gracefully (maybe print a message) if any of its imports are unavailable due to earlier errors
    (Just <$> loadModule name path src imports) `catchError` \ err -> Nothing <$ outputDocLn (prettyNotice err)
  let nSuccess = length (catMaybes results)
      status
        | nModules == nSuccess = annotate Success (pretty nModules)
        | otherwise            = annotate Failure (ratio nSuccess nModules)
  outputDocLn (fillSep [status, reflow "modules loaded."])
  where
  ratio n d = pretty n <+> pretty "of" <+> pretty d
  toNode h@(ModuleHeader n _ _ imports) = let imports' = map (Import.name . S.out) imports in Node n imports' (h{ imports = imports' } :: ModuleHeader MName)

data ModuleHeader a = ModuleHeader
  { moduleName :: MName
  , path       :: FilePath
  , source     :: Source
  , imports    :: [a]
  }
  deriving (Foldable, Functor, Traversable)

loadModuleHeader :: (Has (Output :+: Throw (Notice.Notice (Doc Style))) sig m, MonadIO m) => [FilePath] -> Either FilePath MName -> m (ModuleHeader (S.Ann S.Import))
loadModuleHeader searchPaths target = do
  path <- case target of
    Left path  -> pure path
    Right name -> resolveName searchPaths name
  src <- rethrowIOErrors [] $ readSourceFromFile path
  -- FIXME: validate that the name matches
  (name', is) <- rethrowParseErrors @Style (runParserWithSource src (runFacet [] (whiteSpace *> moduleHeader)))
  pure (ModuleHeader name' path src is)

loadModule :: Has (Output :+: State Options :+: State Target :+: Throw (Notice.Notice (Doc Style)) :+: Write (Notice.Notice (Doc Style))) sig m => MName -> FilePath -> Source -> [MName] -> m Module
loadModule name path src imports = do
  graph <- use modules_
  let ops = foldMap (\ name -> lookupM name graph >>= maybe [] pure . snd >>= map (\ (op, assoc) -> (name, op, assoc)) . operators) imports
  m <- rethrowParseErrors @Style (runParserWithSource src (runFacet (map makeOperator ops) (whole module')))
  opts <- get
  m <- rethrowElabWarnings . rethrowElabErrors opts . runReader graph . runReader src $ Elab.elabModule m
  modules_.at name .= Just (Just path, Just m)
  pure m

resolveName :: (Has (Throw (Notice.Notice (Doc Style))) sig m, MonadIO m) => [FilePath] -> MName -> m FilePath
resolveName searchPaths name = do
  let namePath = toPath name FP.<.> ".facet"
  path <- liftIO $ findFile searchPaths namePath
  case path of
    Just path -> pure path
    Nothing   -> throwError @(Notice.Notice (Doc Style)) $ Notice.Notice (Just Notice.Error) [] (fillSep [pretty "module", squotes (prettyMName name), reflow "could not be found."]) $ case searchPaths of
      [] -> []
      _  -> [ nest 2 (reflow "search paths:" <\> concatWith (<\>) (map pretty searchPaths)) ]
  where
  toPath components = foldr1 (FP.</>) (TS.unpack <$> components)


-- Errors

rethrowIOErrors :: (Has (Throw (Notice.Notice (Doc Style))) sig m, MonadIO m) => [Source] -> IO a -> m a
rethrowIOErrors refs m = liftIO (tryIOError m) >>= either (throwError . ioErrorToNotice refs) pure

ioErrorToNotice :: [Source] -> IOError -> Notice.Notice (Doc Style)
ioErrorToNotice refs err = Notice.Notice (Just Notice.Error) refs (group (reflow (show err))) []

rethrowGraphErrors :: [Source] -> I.ThrowC (Notice.Notice (Doc Style)) GraphErr m a -> m a
rethrowGraphErrors refs = I.runThrow formatGraphErr
  where
  formatGraphErr (CyclicImport path) = Notice.Notice (Just Notice.Error) refs (reflow "cyclic import") (map prettyMName (toList path))
