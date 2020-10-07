{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
module Facet.GHCI
( -- * Parsing
  parseString
, printFile
, elabString
, elabFile
  -- * Pretty-printing
, prettyAnn
  -- * Errors
, toNotice
) where

import           Control.Carrier.Parser.Church (Input(..), ParserC, errToNotice, run, runParser, runParserWithFile, runParserWithString)
import           Control.Carrier.Lift (runM)
import           Control.Carrier.Throw.Either (runThrow)
import           Control.Effect.Parser.Excerpt (fromSourceAndSpan)
import           Control.Effect.Parser.Notice (Level(..), Notice(..), prettyNotice)
import           Control.Effect.Parser.Source (Source(..), sourceFromString)
import           Control.Effect.Parser.Span (Pos(..), Span(..))
import           Control.Monad.IO.Class (MonadIO(..))
import           Data.Bifunctor
import qualified Facet.Core as C
import qualified Facet.Core.Module as Module
import qualified Facet.Core.Type as T
import           Facet.Elab
import           Facet.Parser (Facet(..), module', runFacet, whole)
import qualified Facet.Pretty as P
import qualified Facet.Print as P
import qualified Facet.Surface.Module as S
import           Facet.Syntax ((:::)(..))
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as ANSI
import qualified Silkscreen as S

-- Parsing

parseString :: MonadIO m => Facet (ParserC (Either Notice)) P.Print -> String -> m ()
parseString p s = either (P.putDoc . prettyNotice) P.prettyPrint (runParserWithString (Pos 0 0) s (runFacet mempty mempty p))

printFile :: MonadIO m => FilePath -> m ()
printFile path = runM (runThrow (runParserWithFile path (runFacet mempty mempty (whole module')))) >>= \case
  Left err -> P.putDoc (prettyNotice err)
  Right m  -> P.prettyPrint (P.printSurfaceModule m)


elabString :: MonadIO m => Facet (ParserC (Either Notice)) S.Module -> String -> m ()
elabString = elabPathString Nothing

elabFile :: MonadIO m => FilePath -> m ()
elabFile path = liftIO (readFile path) >>= elabPathString (Just path) module'

elabPathString :: MonadIO m => Maybe FilePath -> Facet (ParserC (Either Notice)) S.Module -> String -> m ()
elabPathString path p s = case parsed >>= first (\ (s, p) -> toNotice (Just Error) src s p []) . run . elab (Span (Pos 0 0) (Pos 0 0)) implicit mempty . elabModule of
  Left err -> P.putDoc (prettyNotice err)
  Right a  -> P.prettyPrint (Module.interpretModule a)
  where
  input = Input (Pos 0 0) s
  src = sourceFromString path s
  parsed = runParser (const Right) failure failure input (runFacet mempty mempty (whole p))
  failure = Left . errToNotice src


-- Pretty-printing

prettyAnn :: (S.Printer p, C.Type p) => (p ::: T.Type) -> p
prettyAnn (tm ::: ty) = tm S.<+> S.colon S.<+> T.interpret ty


-- Errors

toNotice :: Maybe Level -> Source -> Span -> P.Print -> [PP.Doc ANSI.AnsiStyle] -> Notice
toNotice lvl src span = Notice lvl (fromSourceAndSpan src span) . P.getPrint
