module Facet.Run
( runFile
) where

import           Control.Carrier.Error.Church
import           Control.Carrier.State.Church
import           Data.Foldable (for_)
import qualified Data.Set as Set
import           Facet.Carrier.Output.IO
import           Facet.Carrier.Time.System
import           Facet.Carrier.Write.General
import           Facet.Driver
import           Facet.Graph
import           Facet.Print (quietOptions)
import           Facet.Style
import qualified Facet.Surface as Import (Import(..))
import qualified Facet.Surface as S
import           System.Exit

runFile :: [FilePath] -> FilePath -> IO ExitCode
runFile searchPaths path = runStack $ do
  targetHead <- loadModuleHeader searchPaths (Left path)
  modules <- rethrowGraphErrors [] $ loadOrder (fmap toNode . loadModuleHeader searchPaths . Right) [toNode targetHead]
  -- FIXME: look up and evaluate the main function in the module we were passed?
  ExitSuccess <$ for_ modules (\ (name, path, src, imports) -> loadModule name path src imports)
  where
  toNode (ModuleHeader n path source imports) = let imports' = map (Import.name . S.out) imports in Node n imports' (n, path, source, imports')
  runStack
    = runOutput
    . runTime
    . evalState (Target mempty mempty (Set.fromList searchPaths))
    . runError ((ExitFailure 1 <$) . outputDocLn . prettyNotice) pure
    . runWrite (outputDocLn . prettyNotice)
    . evalState quietOptions
