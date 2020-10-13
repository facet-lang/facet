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
import           Control.Carrier.Throw.Either
import           Control.Effect.Parser.Excerpt (fromSourceAndSpan)
import qualified Control.Effect.Parser.Notice as N
import           Control.Effect.Parser.Source (Source(..), sourceFromString)
import           Control.Effect.Parser.Span (Pos(Pos))
import           Control.Monad ((<=<))
import           Control.Monad.IO.Class (MonadIO(..))
import           Data.Semigroup (stimes)
import           Facet.Context
import qualified Facet.Core.Value as V
import           Facet.Elab (Err(..), ErrDoc, M(..), Reason(..), Type, Val, elabModule)
import           Facet.Name (Index(..), Level(..))
import           Facet.Parser (Facet(..), module', runFacet, whole)
import qualified Facet.Pretty as P
import qualified Facet.Print as P
import           Facet.Stack
import qualified Facet.Surface.Module as S
import           Facet.Syntax
import           GHC.Stack
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
    evalMeta $ rethrow $ P.printCoreModule mod
  where
  input = Input (Pos 0 0) s
  src = sourceFromString path s
  failure = Left . errToNotice src
  mkNotice p = toNotice (Just N.Error) src p

  evalMeta = evalState (Metacontext [] :: Metacontext (Val Level ::: Type Level))

  lower :: Either (Err Level) a -> Either N.Notice a
  lower = \case
    Left  e -> do
      e' <- lower $ evalMeta $ rethrow $ mkNotice e
      throwError e'
    Right a -> pure a


-- Errors

toNotice :: Maybe N.Level -> Source -> Err Level -> M Level N.Notice
toNotice lvl src Err{ span, reason, metacontext, context } = do
  reason' <- printReason metacontext context reason
  -- FIXME: print the context
  pure $ N.Notice lvl (fromSourceAndSpan src span) reason' []


printReason :: Metacontext (Val Level ::: Type Level) -> Context (Val Level ::: Type Level) -> Reason Level -> M Level ErrDoc
printReason (Metacontext mctx) ctx = fmap group . \case
  FreeVariable n         -> pure $ fillSep [P.reflow "variable not in scope:", pretty n]
  CouldNotSynthesize msg -> pure $ P.reflow "could not synthesize a type for" <> softline <> P.reflow msg
  Mismatch msg exp act   -> do
    (mctx', ctx') <- V.mapValueAll (ty . ty <$> mctx) (ty . ty <$> elems ctx)
    exp' <- either (pure . P.reflow) (printTypeInContext mctx' ctx') exp
    act' <- printTypeInContext mctx' ctx' act
    pure $ P.reflow msg
      </> pretty "expected:" <> print exp'
      </> pretty "  actual:" <> print act'
    where
    -- line things up nicely for e.g. wrapped function types
    print = nest 2 . (flatAlt (line <> stimes (3 :: Int) space) mempty <>)
  Hole n _T              -> do
    (mctx', ctx') <- V.mapValueAll (ty . ty <$> mctx) (ty . ty <$> elems ctx)
    _T' <- printTypeInContext mctx' ctx' _T
    pure $ fillSep [P.reflow "found hole", pretty n, colon, _T' ]
  BadContext n           -> pure $ fillSep [ P.reflow "no variable bound for index", pretty (getIndex n), P.reflow "in context of length", pretty (getLevel (level ctx)) ]


printTypeInContext :: HasCallStack => [V.Value (M Level) P.Print] -> Stack (V.Value (M Level) P.Print) -> Type Level -> M Level ErrDoc
printTypeInContext mctx ctx = fmap P.getPrint . (P.printCoreValue (Level 0) <=< rethrow . V.mapValue mctx ctx)
