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
import           Control.Carrier.State.Church (evalState)
import           Control.Carrier.Throw.Either (runThrow)
import           Control.Effect.Parser.Excerpt (fromSourceAndSpan)
import qualified Control.Effect.Parser.Notice as N
import           Control.Effect.Parser.Source (Source(..), sourceFromString)
import           Control.Effect.Parser.Span (Pos(..))
import           Control.Monad.IO.Class (MonadIO(..))
import           Data.Bifunctor
import           Facet.Elab (Metacontext(..), Type, Val, elabModule, rethrow)
import           Facet.Error
import           Facet.Name (Index, Level)
import           Facet.Parser (Facet(..), module', runFacet, whole)
import qualified Facet.Pretty as P
import qualified Facet.Print as P
import qualified Facet.Surface.Module as S
import           Facet.Syntax
import           Text.Parser.Position (Spanned)

-- Parsing

parseString :: MonadIO m => Facet (ParserC (Either N.Notice)) P.Print -> String -> m ()
parseString p s = either (P.putDoc . N.prettyNotice) P.prettyPrint (runParserWithString (Pos 0 0) s (runFacet [] p))

printFile :: MonadIO m => FilePath -> m ()
printFile path = runM (runThrow (runParserWithFile path (runFacet [] (whole module')))) >>= \case
  Left err -> P.putDoc (N.prettyNotice err)
  Right m  -> P.prettyPrint (P.printSurfaceModule (snd m))

parseFile :: MonadIO m => FilePath -> m (Either N.Notice (Spanned (S.Module Spanned Index)))
parseFile path = runM (runThrow (runParserWithFile path (runFacet [] (whole module'))))


-- Elaborating

elabString :: MonadIO m => Facet (ParserC (Either N.Notice)) (Spanned (S.Module Spanned Index)) -> String -> m ()
elabString = elabPathString Nothing

elabFile :: MonadIO m => FilePath -> m ()
elabFile path = liftIO (readFile path) >>= elabPathString (Just path) module'

elabPathString :: MonadIO m => Maybe FilePath -> Facet (ParserC (Either N.Notice)) (Spanned (S.Module Spanned Index)) -> String -> m ()
elabPathString path p s = either (P.putDoc . N.prettyNotice) P.prettyPrint $ do
  parsed <- runParser (const Right) failure failure input (runFacet [] (whole p))
  first mkNotice $ do
    mod <- elabModule parsed
    evalState (Metacontext [] :: Metacontext (Val Level ::: Type Level)) $ rethrow $ (P.printCoreModule mod)
  where
  input = Input (Pos 0 0) s
  src = sourceFromString path s
  failure = Left . errToNotice src
  mkNotice p = toNotice (Just N.Error) src p


-- Errors

toNotice :: Maybe N.Level -> Source -> Err -> N.Notice
toNotice lvl src Err{ span, reason, context } = N.Notice lvl (fromSourceAndSpan src span) reason context
