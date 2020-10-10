{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeOperators #-}
module Facet.GHCI
( -- * Parsing
  parseString
, printFile
, elabString
, elabFile
  -- * Errors
, toNotice
) where

import           Control.Carrier.Lift (runM)
import           Control.Carrier.Parser.Church (Input(..), ParserC, errToNotice, run, runParser, runParserWithFile, runParserWithString)
import           Control.Carrier.Throw.Either (runThrow)
import           Control.Effect.Parser.Excerpt (fromSourceAndSpan)
import           Control.Effect.Parser.Notice (Level(..), Notice(..), prettyNotice)
import           Control.Effect.Parser.Source (Source(..), sourceFromString)
import           Control.Effect.Parser.Span (Pos(..), Span(..))
import           Control.Monad.IO.Class (MonadIO(..))
import           Data.Bifunctor
import           Facet.Elab (elab, elabModule, runErrM)
import           Facet.Error
import           Facet.Parser (Facet(..), module', runFacet, whole)
import qualified Facet.Pretty as P
import qualified Facet.Print as P
import qualified Facet.Surface.Module as S

-- Parsing

parseString :: MonadIO m => Facet (ParserC (Either Notice)) P.Print -> String -> m ()
parseString p s = either (P.putDoc . prettyNotice) P.prettyPrint (runParserWithString (Pos 0 0) s (runFacet [] p))

printFile :: MonadIO m => FilePath -> m ()
printFile path = runM (runThrow (runParserWithFile path (runFacet [] (whole module')))) >>= \case
  Left err -> P.putDoc (prettyNotice err)
  Right m  -> P.prettyPrint (P.printSurfaceModule m)


elabString :: MonadIO m => Facet (ParserC (Either Notice)) S.Module -> String -> m ()
elabString = elabPathString Nothing

elabFile :: MonadIO m => FilePath -> m ()
elabFile path = liftIO (readFile path) >>= elabPathString (Just path) module'

elabPathString :: MonadIO m => Maybe FilePath -> Facet (ParserC (Either Notice)) S.Module -> String -> m ()
elabPathString path p s = case parsed >>= first mkNotice . run . elab (Span (Pos 0 0) (Pos 0 0)) mempty . elabModule >>= first mkNotice . runErrM (Span (Pos 0 0) (Pos 0 0)) . P.printCoreModule of
  Left err -> P.putDoc (prettyNotice err)
  Right a  -> P.prettyPrint a
  where
  input = Input (Pos 0 0) s
  src = sourceFromString path s
  parsed = runParser (const Right) failure failure input (runFacet [] (whole p))
  failure = Left . errToNotice src
  mkNotice (s, p) = toNotice (Just Error) src s p


-- Errors

toNotice :: Maybe Level -> Source -> Span -> Err -> Notice
toNotice lvl src span Err{ reason, context } = Notice lvl (fromSourceAndSpan src span) reason context
