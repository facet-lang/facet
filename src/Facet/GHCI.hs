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
  -- * Errors
, toNotice
) where

import           Control.Carrier.Lift (runM)
import           Control.Carrier.Parser.Church (Input(..), ParserC, errToNotice, runParser, runParserWithFile, runParserWithString)
import           Control.Carrier.Reader (runReader)
import           Control.Carrier.Throw.Either (runThrow)
import           Control.Effect.Parser.Excerpt (fromSourceAndSpan)
import           Control.Effect.Parser.Notice (Level(..), Notice(..), prettyNotice)
import           Control.Effect.Parser.Source (Source(..), sourceFromString)
import           Control.Effect.Parser.Span (Pos(..))
import           Control.Monad.IO.Class (MonadIO(..))
import           Data.Bifunctor
import           Facet.Elab (elabModule, rethrow)
import           Facet.Error
import           Facet.Name (Index)
import           Facet.Parser (Facet(..), module', runFacet, whole)
import qualified Facet.Pretty as P
import qualified Facet.Print as P
import qualified Facet.Surface.Module as S
import           Text.Parser.Position (Spanned)

-- Parsing

parseString :: MonadIO m => Facet (ParserC (Either Notice)) P.Print -> String -> m ()
parseString p s = either (P.putDoc . prettyNotice) P.prettyPrint (runParserWithString (Pos 0 0) s (runFacet [] p))

printFile :: MonadIO m => FilePath -> m ()
printFile path = runM (runThrow (runParserWithFile path (runFacet [] (whole module')))) >>= \case
  Left err -> P.putDoc (prettyNotice err)
  Right m  -> P.prettyPrint (P.printSurfaceModule (snd m))

parseFile :: MonadIO m => FilePath -> m (Either Notice (Spanned (S.Module Spanned Index)))
parseFile path = runM (runThrow (runParserWithFile path (runFacet [] (whole module'))))


-- Elaborating

elabString :: MonadIO m => Facet (ParserC (Either Notice)) (Spanned (S.Module Spanned Index)) -> String -> m ()
elabString = elabPathString Nothing

elabFile :: MonadIO m => FilePath -> m ()
elabFile path = liftIO (readFile path) >>= elabPathString (Just path) module'

elabPathString :: MonadIO m => Maybe FilePath -> Facet (ParserC (Either Notice)) (Spanned (S.Module Spanned Index)) -> String -> m ()
elabPathString path p s = either (P.putDoc . prettyNotice) P.prettyPrint $ do
  (s, parsed) <- runParser (const Right) failure failure input (runFacet [] (whole p))
  first mkNotice $ rethrow $ do
    mod <- runReader s $ elabModule (s, parsed)
    P.printCoreModule mod
  where
  input = Input (Pos 0 0) s
  src = sourceFromString path s
  failure = Left . errToNotice src
  mkNotice p = toNotice (Just Error) src p


-- Errors

toNotice :: Maybe Level -> Source -> Err -> Notice
toNotice lvl src Err{ span, reason, context } = Notice lvl (fromSourceAndSpan src span) reason context
