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
  -- * Smart constructors
, makeType
, _Type
, (>=>)
, (-->)
) where

import           Control.Applicative (liftA2)
import           Control.Carrier.Lift (runM)
import           Control.Carrier.Parser.Church (Has, Input(..), ParserC, errToNotice, run, runParser, runParserWithFile, runParserWithString)
import           Control.Carrier.Reader (Reader, ReaderC, asks, local, runReader)
import           Control.Carrier.Throw.Either (runThrow)
import           Control.Effect.Parser.Excerpt (fromSourceAndSpan)
import           Control.Effect.Parser.Notice (Level(..), Notice(..), prettyNotice)
import           Control.Effect.Parser.Source (Source(..), sourceFromString)
import           Control.Effect.Parser.Span (Pos(..), Span(..))
import           Control.Monad.IO.Class (MonadIO(..))
import           Data.Bifunctor
import           Data.Functor.Identity
import           Data.Text (pack)
import qualified Facet.Core as C
import qualified Facet.Core.Type as T
import           Facet.Elab (elab, elabModule, implicit)
import           Facet.Name (Name(..))
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
  Right a  -> P.prettyPrint (P.printCoreModule a)
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


-- Smart constructors

makeType :: ReaderC Int Identity T.Type -> T.Type
makeType = run . runReader 0

_Type :: Applicative m => m T.Type
_Type = pure C._Type

(>=>) :: Has (Reader Int) sig m => (String ::: m T.Type) -> (m T.Type -> m T.Type) -> m T.Type
s ::: t >=> b = do
  n <- asks (Name (pack s))
  (C.>=>) . (n :::) <$> t <*> local (+ (1 :: Int)) (b (pure (C.tbound n)))

infixr 1 >=>

(-->) :: Applicative m => m T.Type -> m T.Type -> m T.Type
(-->) = liftA2 (C.-->)

infixr 1 -->
