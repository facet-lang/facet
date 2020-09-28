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
) where

import           Control.Carrier.Lift
import           Control.Carrier.Parser.Church (ParserC, runParserWithString)
import           Control.Carrier.Throw.Either (ThrowC, runThrow)
import           Control.Effect.Parser.Notice (Notice, prettyNotice)
import           Control.Effect.Parser.Span (Pos(..))
import           Control.Monad.IO.Class (MonadIO(..))
import           Data.Bifunctor
import qualified Facet.Core.Lifted as C
import           Facet.Elab
import qualified Facet.Pretty as P
import           Facet.Name
import qualified Facet.Print as P
import           Facet.Syntax ((:::)(..))
import qualified Facet.Type as T
import qualified Silkscreen as S

-- Parsing

parseString' :: MonadIO m => ParserC (ThrowC Notice (LiftC m)) P.Print -> String -> m ()
parseString' p s = runM $ do
  r <- runThrow (runParserWithString (Pos 0 0) s p)
  either (P.putDoc . prettyNotice) P.prettyPrint r

parseElabString :: (MonadIO m, C.Type e) => ParserC (ThrowC Notice (LiftC m)) (Elab e P.Print) -> String -> m ()
parseElabString p s = runM $
  runThrow (runParserWithString (Pos 0 0) s p) >>= \ r -> case first prettyNotice r >>= first (P.prettyWith P.terminalStyle) . elab . (::: Nothing) of
    Left err -> P.putDoc err
    Right a -> P.prettyPrint a


-- Elaboration

printElab :: Synth (T.Type ::: T.Type) -> IO ()
printElab = P.prettyPrint . either id prettyAnn . runSynth

prettyAnn :: (S.Printer p, C.Type p) => (T.Type ::: T.Type) -> p
prettyAnn (tm ::: ty) = C.interpret tm S.<+> S.colon S.<+> C.interpret ty

thing :: Synth (T.Type ::: T.Type)
thing = (__ ::: switch (switch _Type --> switch _Type)) >=> \ t -> switch (switch (pure t .$ switch _Unit) --> switch (pure t .$ switch _Unit))
