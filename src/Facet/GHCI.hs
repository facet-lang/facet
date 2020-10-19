{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Facet.GHCI
( -- * Parsing
  parseString
, printFile
, parseFile
  -- * Elaborating
, elabString
, elabFile
) where

import           Control.Carrier.Lift (runM)
import           Control.Carrier.Throw.Either
import           Control.Monad.IO.Class (MonadIO(..))
import           Facet.Algebra (foldCModule, foldSModule)
import           Facet.Carrier.Parser.Church as Parse (Err, ParserC, runParserWithFile, runParserWithSource, runParserWithString)
import qualified Facet.Carrier.Throw.Inject as L
import           Facet.Elab as Elab (elabModule)
import           Facet.Notice
import           Facet.Notice.Elab
import           Facet.Notice.Parser
import           Facet.Parser (Facet(..), module', runFacet, whole)
import qualified Facet.Pretty as P
import qualified Facet.Print as P
import           Facet.Source (Source(..), sourceFromString)
import qualified Facet.Surface as S
import qualified System.Console.ANSI as ANSI
import           Text.Parser.Position (Spanned)

-- Parsing

parseString :: MonadIO m => Facet (ParserC (L.ThrowC (Notice [ANSI.SGR]) (Source, Parse.Err) (Either (Notice [ANSI.SGR])))) P.Print -> String -> m ()
parseString p s = either (P.putDoc . prettyNotice) P.prettyPrint (rethrowParseErrors (runParserWithString 0 s (runFacet [] p)))

printFile :: MonadIO m => FilePath -> m ()
printFile path = runM (runThrow (rethrowParseErrors (runParserWithFile path (runFacet [] (whole module'))))) >>= \case
  Left err -> P.putDoc (prettyNotice err)
  Right m  -> P.prettyPrint (foldSModule P.surface m)

parseFile :: MonadIO m => FilePath -> m (Either (Notice [ANSI.SGR]) (Spanned S.Module))
parseFile path = runM (runThrow (rethrowParseErrors (runParserWithFile path (runFacet [] (whole module')))))


-- Elaborating

elabString :: MonadIO m => Facet (ParserC (L.ThrowC (Notice [ANSI.SGR]) (Source, Parse.Err) (Either (Notice [ANSI.SGR])))) (Spanned S.Module) -> String -> m ()
elabString = elabPathString Nothing

elabFile :: MonadIO m => FilePath -> m ()
elabFile path = liftIO (readFile path) >>= elabPathString (Just path) module'

elabPathString :: MonadIO m => Maybe FilePath -> Facet (ParserC (L.ThrowC (Notice [ANSI.SGR]) (Source, Parse.Err) (Either (Notice [ANSI.SGR])))) (Spanned S.Module) -> String -> m ()
elabPathString path p s = either (P.putDoc . prettyNotice) P.prettyPrint $ do
  parsed <- rethrowParseErrors $ runParserWithSource src (runFacet [] (whole p))
  rethrowElabErrors src $ foldCModule P.explicit <$> elabModule parsed
  where
  src = sourceFromString path 0 s
