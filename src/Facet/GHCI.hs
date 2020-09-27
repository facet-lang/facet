{-# LANGUAGE TypeOperators #-}
module Facet.GHCI
( -- * Parsing
  parseString'
  -- * Elaboration
, printElab
, thing
) where

import           Control.Carrier.Parser.Church (Algebra, ParserC, runParserWithString)
import           Control.Carrier.Throw.Either (ThrowC, runThrow)
import           Control.Effect.Parser.Notice (Notice, prettyNotice)
import           Control.Effect.Parser.Span (Pos(..))
import           Control.Monad.IO.Class (MonadIO(..))
import qualified Facet.Core.Lifted as C
import           Facet.Elab
import           Facet.Env (strengthen)
import qualified Facet.Pretty as P
import           Facet.Functor.I (I(..))
import qualified Facet.Print as P
import           Facet.Syntax ((:::)(..))
import qualified Facet.Type as T
import qualified Silkscreen as S

-- Parsing

parseString' :: (Algebra sig m, MonadIO m) => ParserC (ThrowC Notice m) P.Print -> String -> m ()
parseString' p s = do
  r <- runThrow (runParserWithString (Pos 0 0) s p)
  either (P.putDoc . prettyNotice) P.prettyPrint r


-- Elaboration

printElab :: Synth (I T.Type ::: T.Type) -> IO ()
printElab = either P.prettyPrint (\ (I tm ::: ty) -> P.prettyPrint (P.runTPrint (C.interpret (T.inst tm)) S.<+> S.colon S.<+> P.runTPrint (C.interpret (T.inst ty)))) . runSynth

thing :: Synth (I T.Type ::: T.Type)
thing = strengthen (switch (switch _Type --> switch _Type)) >=> \ _ t -> switch (switch (pure t .$ switch _Unit) --> switch (pure t .$ switch _Unit))
