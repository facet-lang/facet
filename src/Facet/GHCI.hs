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
import           Control.Carrier.Reader (runReader)
import           Control.Carrier.Throw.Either
import           Control.Monad.IO.Class (MonadIO(..))
import           Facet.Algebra (foldCModule, foldSModule)
import           Facet.Carrier.Parser.Church as Parse (Err, ParserC, runParserWithFile, runParserWithSource, runParserWithString)
import qualified Facet.Carrier.Throw.Inject as L
import           Facet.Elab as Elab (elabModule)
import           Facet.Graph (Graph)
import           Facet.Notice
import           Facet.Notice.Elab
import           Facet.Notice.Parser
import           Facet.Parser (Facet(..), module', runFacet, whole)
import qualified Facet.Pretty as P
import qualified Facet.Print as P
import           Facet.Source (Source(..), sourceFromString)
import           Facet.Style
import qualified Facet.Surface as S
import           Prettyprinter (reAnnotate)

-- Parsing

parseString :: MonadIO m => Facet (ParserC (L.ThrowC (Notice Style) (Source, Parse.Err) (Either (Notice Style)))) P.Print -> String -> m ()
parseString p s = either printNotice printCode (rethrowParseErrors (runParserWithString 0 s (runFacet [] [] p)))

printFile :: MonadIO m => FilePath -> m ()
printFile path = runM (runThrow (rethrowParseErrors @Style (runParserWithFile path (runFacet [] [] (whole module'))))) >>= \case
  Left err -> printNotice err
  Right m  -> printCode (foldSModule P.surface m)

parseFile :: MonadIO m => FilePath -> m (Either (Notice Style) (S.Ann S.Module))
parseFile path = runM (runThrow (rethrowParseErrors @Style (runParserWithFile path (runFacet [] [] (whole module')))))


-- Elaborating

elabString :: MonadIO m => Facet (ParserC (L.ThrowC (Notice Style) (Source, Parse.Err) (Either (Notice Style)))) (S.Ann S.Module) -> String -> m ()
elabString = elabPathString Nothing

elabFile :: MonadIO m => FilePath -> m ()
elabFile path = liftIO (readFile path) >>= elabPathString (Just path) module'

elabPathString :: MonadIO m => Maybe FilePath -> Facet (ParserC (L.ThrowC (Notice Style) (Source, Parse.Err) (Either (Notice Style)))) (S.Ann S.Module) -> String -> m ()
elabPathString path p s = either printNotice printCode $ do
  parsed <- rethrowParseErrors $ runParserWithSource src (runFacet [] [] (whole p))
  rethrowElabErrors src Code . runReader @Graph mempty $ foldCModule P.explicit <$> elabModule parsed
  where
  src = sourceFromString path 0 s


printNotice :: MonadIO m => Notice Style -> m ()
printNotice = P.putDoc . reAnnotate (terminalNoticeStyle . fmap terminalStyle) . prettyNotice

printCode :: MonadIO m => P.Print -> m ()
printCode = P.putDoc . reAnnotate terminalCodeStyle . P.getPrint
