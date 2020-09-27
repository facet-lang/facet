{-# LANGUAGE TypeOperators #-}
module Facet.GHCI
( printElab
) where

import qualified Data.Kind as K
import qualified Facet.Core.Typed.Lifted as CT
import           Facet.Elab
import           Facet.Env
import           Facet.Functor.I
import qualified Facet.Print as P
import           Facet.Syntax.Common
import qualified Facet.Type.Typed as T
import qualified Silkscreen as S

printElab :: Synth (I (ForAll1 T.Type ((K.Type -> K.Type) -> K.Type)) ::: ForAll1 T.Type K.Type) -> IO ()
printElab = either P.prettyPrint (\ (I tm ::: ty) -> P.prettyPrint (P.runTPrint (CT.interpret (instantiate1 tm)) S.<+> S.colon S.<+> P.runTPrint (CT.interpret (instantiate1 ty)))) . runSynth
