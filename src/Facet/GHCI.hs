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
import           Control.Carrier.Parser.Church as Parse (Err, ParserC, errToNotice, runParserWithFile, runParserWithSource, runParserWithString)
import           Control.Carrier.Throw.Either
import qualified Control.Effect.Parser.Notice as N
import           Control.Effect.Parser.Source (Source(..), slice, sourceFromString)
import           Control.Monad.IO.Class (MonadIO(..))
import           Data.Foldable (toList)
import           Data.Semigroup (stimes)
import           Facet.Algebra (foldCModule, foldCValue, foldSModule)
import qualified Facet.Carrier.Throw.Inject as L
import           Facet.Context
import           Facet.Elab as Elab (Err(..), Reason(..), Type, elabModule)
import           Facet.Name (Index(..), Level(..))
import           Facet.Notice
import           Facet.Parser (Facet(..), module', runFacet, whole)
import qualified Facet.Pretty as P
import qualified Facet.Print as P
import           Facet.Stack (Stack(..))
import qualified Facet.Surface as S
import           Facet.Syntax
import qualified Prettyprinter as PP
import           Silkscreen (colon, fillSep, flatAlt, group, line, nest, pretty, softline, space, (</>))
import qualified System.Console.ANSI as ANSI
import           Text.Parser.Position (Spanned)

-- Parsing

parseString :: MonadIO m => Facet (ParserC (L.ThrowC (Notice [ANSI.SGR]) (Source, Parse.Err) (Either (Notice [ANSI.SGR])))) P.Print -> String -> m ()
parseString p s = either (P.putDoc . prettyNotice) P.prettyPrint (rethrowParseErrors(runParserWithString 0 s (runFacet [] p)))

printFile :: MonadIO m => FilePath -> m ()
printFile path = runM (runThrow (runParserWithFile path (runFacet [] (whole module')))) >>= \case
  Left err -> P.putDoc (prettyNotice (uncurry errToNotice err))
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
  L.runThrow mkNotice $ foldCModule P.explicit <$> elabModule parsed
  where
  src = sourceFromString path 0 s
  mkNotice p = toNotice (Just N.Error) src p


-- Errors

rethrowParseErrors :: L.ThrowC (Notice [ANSI.SGR]) (Source, Parse.Err) m a -> m a
rethrowParseErrors = L.runThrow (uncurry errToNotice)

toNotice :: Maybe N.Level -> Source -> Elab.Err -> Notice [ANSI.SGR]
toNotice lvl src Err{ span, reason, context } =
  let reason' = printReason context reason
  in Notice lvl (slice src span) reason' $
    [ P.getPrint $ P.printContextEntry l (n ::: foldCValue P.explicit Nil _T)
    | (l, n ::: _T) <- zip [Level 0..] (toList (elems context))
    ]
    -- FIXME: foldl over the context printing each element in the smaller context before it.


printReason :: Context Type -> Reason -> PP.Doc [ANSI.SGR]
printReason ctx = group . \case
  FreeVariable n         -> fillSep [P.reflow "variable not in scope:", pretty n]
  CouldNotSynthesize msg -> P.reflow "could not synthesize a type for" <> softline <> P.reflow msg
  Mismatch msg exp act   ->
    let exp' = either P.reflow (printType Nil) exp
        act' = printType Nil act
    in P.reflow msg
      </> pretty "expected:" <> print exp'
      </> pretty "  actual:" <> print act'
    where
    -- line things up nicely for e.g. wrapped function types
    print = nest 2 . (flatAlt (line <> stimes (3 :: Int) space) mempty <>)
  Hole n _T              ->
    let _T' = printType Nil _T
    in fillSep [P.reflow "found hole", pretty n, colon, _T' ]
  BadContext n           -> fillSep [ P.reflow "no variable bound for index", pretty (getIndex n), P.reflow "in context of length", pretty (length ctx) ]
  where
  -- FIXME: foldl over the context printing each element in the smaller context before it.
  env = elems ctx


printType :: Stack P.Print -> Type -> PP.Doc [ANSI.SGR]
printType env = P.getPrint . foldCValue P.explicit env
