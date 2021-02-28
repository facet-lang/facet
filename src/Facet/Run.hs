module Facet.Run
( runFile
) where

import           Control.Carrier.Error.Church
import           Control.Carrier.State.Church
import           Control.Effect.Lens (use, (.=))
import           Control.Lens (at, (^.))
import           Data.Foldable (for_)
import qualified Data.Set as Set
import           Facet.Carrier.Output.IO
import           Facet.Carrier.Time.System
import           Facet.Carrier.Write.General
import           Facet.Driver
import           Facet.Graph
import           Facet.Print (quietOptions)
import           Facet.Style
import           System.Exit

runFile :: [FilePath] -> FilePath -> IO ExitCode
runFile searchPaths path = runStack $ do
  targetHead <- loadModuleHeader searchPaths (Left path)
  modules <- rethrowGraphErrors [] $ loadOrder (fmap headerNode . loadModuleHeader searchPaths . Right) [headerNode targetHead]
  -- FIXME: look up and evaluate the main function in the module we were passed?
  ExitSuccess <$ for_ modules (\ h@(ModuleHeader name _ _ imports) -> do
    modules <- use modules_
    let loaded = traverse (\ name -> modules^.at name >>= snd) imports
    for_ loaded (\ loaded -> do
      (path, m) <- loadModule h{ imports = loaded }
      modules_.at name .= Just (Just path, Just m)
      pure m))
  where
  runStack
    = runOutput
    . runTime
    . evalState (Target mempty mempty (Set.fromList searchPaths))
    . runError ((ExitFailure 1 <$) . outputDocLn . prettyNotice) pure
    . runWrite (outputDocLn . prettyNotice)
    . evalState quietOptions
