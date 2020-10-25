{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Carrier.Readline.Haskeline
( -- * Readline carrier
  runReadline
, runReadlineWithHistory
, ReadlineC(ReadlineC)
  -- * Readline effect
, module Facet.Effect.Readline
) where

import Control.Algebra
import Control.Monad.Catch (MonadMask(..))
import Control.Monad.Fix (MonadFix)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Trans.Class (MonadTrans(..))
import Data.Text.Lazy (unpack)
import Facet.Effect.Readline
import Facet.Pretty
import Facet.Style
import Prettyprinter (reAnnotateS)
import System.Console.Haskeline as H
import System.Directory
import System.Environment
import System.FilePath

runReadline :: (MonadIO m, MonadMask m) => Prefs -> Settings m -> ReadlineC m a -> m a
runReadline prefs settings (ReadlineC m) = runInputTWithPrefs prefs settings m

runReadlineWithHistory :: (MonadIO m, MonadMask m) => ReadlineC m a -> m a
runReadlineWithHistory block = do
  (prefs, settings) <- liftIO $ do
    homeDir <- getHomeDirectory
    prefs   <- readPrefs (homeDir </> ".haskeline")
    prog    <- getExecutablePath
    let settingsDir = homeDir </> ".local" </> dropExtension (takeFileName prog)
        settings = Settings
          { complete       = completeFilename
          , historyFile    = Just (settingsDir </> "repl_history")
          , autoAddHistory = True
          }
    createDirectoryIfMissing True settingsDir
    pure (prefs, settings)

  runReadline prefs settings block

newtype ReadlineC m a = ReadlineC { runReadlineC :: InputT m a }
  deriving (Applicative, Functor, Monad, MonadFix, MonadIO, MonadTrans)

instance (Algebra sig m, MonadIO m, MonadMask m) => Algebra (Readline :+: sig) (ReadlineC m) where
  alg hdl sig ctx = case sig of
    L readline -> case readline of
      GetInputLine prompt -> (<$ ctx) <$> ReadlineC (H.getInputLine prompt)
      OutputDoc d         -> do
        opts <- liftIO layoutOptionsForTerminal
        (<$ ctx) <$> ReadlineC (H.outputStr (unpack (renderLazy (reAnnotateS terminalStyle (layoutSmart opts d)))))
      WithInterrupt m     -> ReadlineC (H.withInterrupt (runReadlineC (hdl (m <$ ctx))))
      HandleInterrupt h m -> ReadlineC (H.handleInterrupt (runReadlineC (hdl (h <$ ctx))) (runReadlineC (hdl (m <$ ctx))))
    R other -> ReadlineC $ H.withRunInBase $ \ run -> alg (run . runReadlineC . hdl) other ctx
