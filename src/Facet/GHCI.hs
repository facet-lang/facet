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
import           Control.Carrier.Throw.Either
import           Control.Effect.Parser.Excerpt (fromSourceAndSpan)
import qualified Control.Effect.Parser.Notice as N
import           Control.Effect.Parser.Source (Source(..), sourceFromString)
import           Control.Effect.Parser.Span (Pos(Pos))
import           Control.Monad.IO.Class (MonadIO(..))
import           Data.Foldable (toList)
import           Data.Semigroup (stimes)
import           Facet.Context
import           Facet.Elab (Err(..), ErrDoc, Reason(..), Type, Val, elabModule)
import           Facet.Name (Index(..), Level(..))
import           Facet.Parser (Facet(..), module', runFacet, whole)
import qualified Facet.Pretty as P
import qualified Facet.Print as P
import qualified Facet.Surface.Module as S
import           Facet.Syntax
import           Silkscreen (colon, fillSep, flatAlt, group, line, nest, pretty, softline, space, (</>))
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
  lower $ do
    mod <- elabModule parsed
    pure $ P.printCoreModule mod
  where
  input = Input (Pos 0 0) s
  src = sourceFromString path s
  failure = Left . errToNotice src
  mkNotice p = toNotice (Just N.Error) src p

  lower :: Either (Err P.Print) a -> Either N.Notice a
  lower = either (throwError . mkNotice) pure


-- Errors

toNotice :: Maybe N.Level -> Source -> Err P.Print -> N.Notice
toNotice lvl src Err{ span, reason, context } =
  let reason' = printReason context reason
  in N.Notice lvl (fromSourceAndSpan src span) reason' $
    [ P.getPrint $ P.printContextEntry (Level l) (n ::: P.printCoreValue (Level l) _T)
    | (l, n ::: _ ::: _T) <- zip [0..] (toList (elems context))
    ]


printReason :: Context (Val P.Print ::: Type P.Print) -> Reason P.Print -> ErrDoc
printReason ctx = group . \case
  FreeVariable n         -> fillSep [P.reflow "variable not in scope:", pretty n]
  CouldNotSynthesize msg -> P.reflow "could not synthesize a type for" <> softline <> P.reflow msg
  Mismatch msg exp act   ->
    let exp' = either P.reflow (printType l) exp
        act' = printType l act
    in P.reflow msg
      </> pretty "expected:" <> print exp'
      </> pretty "  actual:" <> print act'
    where
    -- line things up nicely for e.g. wrapped function types
    print = nest 2 . (flatAlt (line <> stimes (3 :: Int) space) mempty <>)
  Hole n _T              ->
    let _T' = printType l _T
    in fillSep [P.reflow "found hole", pretty n, colon, _T' ]
  BadContext n           -> fillSep [ P.reflow "no variable bound for index", pretty (getIndex n), P.reflow "in context of length", pretty (length ctx) ]
  where
  l = level ctx


printType :: Level -> Type P.Print -> ErrDoc
printType l = P.getPrint . P.printCoreValue l
