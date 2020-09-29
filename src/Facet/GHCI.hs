{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
module Facet.GHCI
( -- * Parsing
  parseString'
, parseElabString
  -- * Elaboration
, printElab
, prettyAnn
, thing
  -- * Errors
, toNotice
) where

import           Control.Carrier.Parser.Church (ParserC, Input(..), errToNotice, runParser, runParserWithString)
import           Control.Effect.Parser.Excerpt (fromSourceAndSpan)
import           Control.Effect.Parser.Notice (Level(..), Notice(..), prettyNotice)
import           Control.Effect.Parser.Source (Source(..), sourceFromString)
import           Control.Effect.Parser.Span (Pos(..), Span(..))
import           Control.Monad.Fix
import           Control.Monad.IO.Class (MonadIO(..))
import           Data.Bifunctor
import           Facet.Carrier.Error.Context
import           Facet.Carrier.Fail.Throw.Print
import qualified Facet.Core.Lifted as C
import           Facet.Elab
import qualified Facet.Pretty as P
import           Facet.Name
import qualified Facet.Print as P
import           Facet.Syntax ((:::)(..))
import qualified Facet.Type as T
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as ANSI
import qualified Silkscreen as S

-- Parsing

parseString' :: MonadIO m => ParserC (Either Notice) P.Print -> String -> m ()
parseString' p s = either (P.putDoc . prettyNotice) P.prettyPrint (runParserWithString (Pos 0 0) s p)

parseElabString :: (MonadIO m, C.Type e) => ParserC (Either Notice) (Elab e (FailC P.Print (ErrorC Span P.Print ((->) Span))) P.Print) -> String -> m ()
parseElabString p s = case parsed >>= first (\ (s, p) -> toNotice (Just Error) src s p []) . ($ (Span (Pos 0 0) (Pos 0 0))) . runError . runFail . elab . (::: Nothing) of
  Left err -> P.putDoc (prettyNotice err)
  Right a -> P.prettyPrint a
  where
  parsed = runParser (const Right) failure failure input p
  src = sourceFromString Nothing s
  failure = Left . errToNotice src
  input = Input (Pos 0 0) s


-- Elaboration

printElab :: C.Type e => Synth e (Either P.Print) (T.Type ::: T.Type) -> IO ()
printElab m = P.prettyPrint (either id prettyAnn (runSynth m implicit))

prettyAnn :: (S.Printer p, C.Type p) => (T.Type ::: T.Type) -> p
prettyAnn (tm ::: ty) = C.interpret tm S.<+> S.colon S.<+> C.interpret ty

thing :: (MonadFail m, MonadFix m) => Synth e m (T.Type ::: T.Type)
thing = (__ ::: switch (switch _Type --> switch _Type)) >=> \ t -> switch (switch (pure t .$ switch _Unit) --> switch (pure t .$ switch _Unit))


-- Errors

toNotice :: Maybe Level -> Source -> Span -> P.Print -> [PP.Doc ANSI.AnsiStyle] -> Notice
toNotice lvl src span = Notice lvl (fromSourceAndSpan src span) . P.prettyWith P.terminalStyle
