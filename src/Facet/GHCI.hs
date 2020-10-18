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
import           Control.Carrier.Parser.Church as Parse (Err, Input(..), ParserC, errToNotice, runParser, runParserWithFile, runParserWithString)
import           Control.Carrier.Throw.Either
import           Control.Effect.Parser.Excerpt (fromSourceAndSpan)
import           Control.Effect.Parser.Notice (Level(..), Style(..))
import qualified Control.Effect.Parser.Notice as N
import           Control.Effect.Parser.Source (Source(..), sourceFromString)
import           Control.Effect.Parser.Span (Pos(Pos))
import           Control.Monad.IO.Class (MonadIO(..))
import           Data.Foldable (toList)
import           Data.Semigroup (stimes)
import           Facet.Algebra (foldCModule, foldCValue, foldSModule)
import           Facet.Context
import           Facet.Core (Value)
import           Facet.Elab as Elab (Err(..), ErrDoc, Reason(..), Type, elabModule)
import           Facet.Name (Index(..), Level(..))
import           Facet.Parser (Facet(..), module', runFacet, whole)
import qualified Facet.Pretty as P
import qualified Facet.Print as P
import           Facet.Stack (Stack(..))
import qualified Facet.Surface as S
import           Facet.Syntax
import           Prettyprinter.Render.Terminal (AnsiStyle, Color(..), bold, color)
import           Silkscreen (annotate, colon, fillSep, flatAlt, group, line, nest, pretty, softline, space, (</>))
import           Text.Parser.Position (Spanned)

-- Parsing

parseString :: MonadIO m => Facet (ParserC (Either (Source, Parse.Err))) P.Print -> String -> m ()
parseString p s = either (P.putDoc . N.prettyNoticeWith ansiStyle . uncurry errToNotice) P.prettyPrint (runParserWithString (Pos 0 0) s (runFacet [] p))

printFile :: MonadIO m => FilePath -> m ()
printFile path = runM (runThrow (runParserWithFile path (runFacet [] (whole module')))) >>= \case
  Left err -> P.putDoc (N.prettyNoticeWith ansiStyle (uncurry errToNotice err))
  Right m  -> P.prettyPrint (foldSModule P.surface m)

parseFile :: MonadIO m => FilePath -> m (Either (Source, Parse.Err) (Spanned S.Module))
parseFile path = runM (runThrow (runParserWithFile path (runFacet [] (whole module'))))


-- Elaborating

elabString :: MonadIO m => Facet (ParserC (Either (N.Notice AnsiStyle))) (Spanned S.Module) -> String -> m ()
elabString = elabPathString Nothing

elabFile :: MonadIO m => FilePath -> m ()
elabFile path = liftIO (readFile path) >>= elabPathString (Just path) module'

elabPathString :: MonadIO m => Maybe FilePath -> Facet (ParserC (Either (N.Notice AnsiStyle))) (Spanned S.Module) -> String -> m ()
elabPathString path p s = either (P.putDoc . N.prettyNoticeWith ansiStyle) P.prettyPrint $ do
  parsed <- runParser (const Right) failure failure input (runFacet [] (whole p))
  lower $ foldCModule P.explicit <$> elabModule parsed
  where
  input = Input (Pos 0 0) s
  src = sourceFromString path s
  failure = Left . errToNotice src
  mkNotice p = toNotice (Just N.Error) src p

  lower :: Either Elab.Err a -> Either (N.Notice AnsiStyle) a
  lower = either (throwError . mkNotice) pure


-- Errors

toNotice :: Maybe N.Level -> Source -> Elab.Err -> N.Notice AnsiStyle
toNotice lvl src Err{ span, reason, context } =
  let reason' = printReason context reason
  in N.Notice lvl (fromSourceAndSpan src span) reason' $
    [ P.getPrint $ P.printContextEntry l (n ::: foldCValue P.explicit Nil _T)
    | (l, n ::: _ ::: _T) <- zip [Level 0..] (toList (elems context))
    ]
    -- FIXME: foldl over the context printing each element in the smaller context before it.


printReason :: Context (Value ::: Type) -> Reason -> ErrDoc
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


printType :: Stack P.Print -> Type -> ErrDoc
printType env = P.getPrint . foldCValue P.explicit env


ansiStyle :: Style AnsiStyle
ansiStyle = Style
  { pathStyle   = annotate bold
  , levelStyle  = \case
    Warn  -> annotate (color Magenta)
    Error -> annotate (color Red)
  , posStyle    = annotate bold
  , gutterStyle = annotate (color Blue)
  , eofStyle    = annotate (color Blue)
  , caretStyle  = annotate (color Green)
  }
