module Facet.CLI
( main
) where

import           Control.Monad (join)
import           Data.Version (showVersion)
import qualified Facet.REPL as REPL
import           Options.Applicative as Options
import qualified Paths_facet as Library (version)

main :: IO ()
main = join (execParser argumentsParser)

argumentsParser :: ParserInfo (IO ())
argumentsParser = info
  (version <*> helper <*> hsubparser commands)
  (  fullDesc
  <> progDesc "Facet is a language featuring algebraic effects and handlers."
  <> header   "Facet - a functional, effectful language")

commands :: Mod CommandFields (IO ())
commands
  =  command "repl" (info (pure REPL.repl) (progDesc "run the repl"))

versionString :: String
versionString = "facetc version " <> showVersion Library.version

version :: Options.Parser (a -> a)
version = infoOption versionString (long "version" <> short 'V' <> help "Output version info.")
