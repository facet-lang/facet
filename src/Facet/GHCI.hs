{-# LANGUAGE TypeOperators #-}
module Facet.GHCI
( printElab
, thing
) where

import qualified Data.Kind as K
import qualified Facet.Core.Lifted as C
import           Facet.Elab
import           Facet.Env
import           Facet.Functor.I
import qualified Facet.Print as P
import           Facet.Syntax.Common
import qualified Facet.Type as T
import qualified Silkscreen as S

printElab :: Synth (I (T.Type ((K.Type -> K.Type) -> K.Type)) ::: T.Type K.Type) -> IO ()
printElab = either P.prettyPrint (\ (I tm ::: ty) -> P.prettyPrint (P.runTPrint (C.interpret (T.inst tm)) S.<+> S.colon S.<+> P.runTPrint (C.interpret (T.inst ty)))) . runSynth

thing :: Synth (I (T.Type ((K.Type -> K.Type) -> K.Type)) ::: T.Type K.Type)
thing = strengthen (switch (switch _Type --> switch _Type)) >=> \ _ t -> switch (switch (pure t .$ switch _Unit) --> switch (pure t .$ switch _Unit))
