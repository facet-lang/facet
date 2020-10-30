-- | Operations driving the loading and processing of modules.
module Facet.Driver
( Target(..)
, modules_
, targets_
, searchPaths_
  -- * Module loading
, loadModuleHeader
, loadModule
, resolveName
) where

import           Control.Carrier.Reader
import           Control.Effect.Lens (use, (.=))
import           Control.Effect.State
import           Control.Effect.Throw
import           Control.Lens (Lens', at, lens)
import           Control.Monad ((<=<))
import           Control.Monad.IO.Class
import           Data.Foldable (toList)
import qualified Data.Set as Set
import qualified Data.Text as TS
import           Facet.Carrier.Parser.Church
import           Facet.Core
import           Facet.Effect.Trace
import qualified Facet.Elab as Elab
import           Facet.Graph
import           Facet.Name
import qualified Facet.Notice as Notice
import           Facet.Notice.Elab (rethrowElabErrors)
import           Facet.Notice.Parser (rethrowParseErrors)
import           Facet.Parser
import           Facet.Pretty
import           Facet.Source
import           Facet.Style
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


-- Module loading

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


-- Errors

rethrowIOErrors :: (Has (Throw (Notice.Notice Style)) sig m, MonadIO m) => Source -> IO a -> m a
rethrowIOErrors src m = liftIO (tryIOError m) >>= either (throwError . ioErrorToNotice src) pure

ioErrorToNotice :: Source -> IOError -> Notice.Notice Style
ioErrorToNotice src err = Notice.Notice (Just Notice.Error) src (group (reflow (show err))) []
