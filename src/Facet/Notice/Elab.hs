module Facet.Notice.Elab
( -- * Elaboration
  rethrowElabErrors
, rethrowElabWarnings
) where

import           Data.Foldable (foldl')
import           Data.Semigroup (stimes)
import qualified Facet.Carrier.Throw.Inject as L
import qualified Facet.Carrier.Write.Inject as L
import           Facet.Context
import           Facet.Core.Type (metas)
import           Facet.Elab as Elab
import           Facet.Notice as Notice
import           Facet.Pretty
import           Facet.Print as Print
import           Facet.Semiring (Few(..), one, zero)
import           Facet.Snoc
import           Facet.Style
import           Facet.Syntax
import           GHC.Stack
import           Prelude hiding (unlines)
import           Silkscreen

-- Elaboration

rethrowElabErrors :: Options -> L.ThrowC (Notice (Doc Style)) Err m a -> m a
rethrowElabErrors opts = L.runThrow rethrow
  where
  rethrow Err{ source, reason, context, subst, callStack } = Notice.Notice (Just Error) [source] (printErrReason opts printCtx reason)
    [ nest 2 (pretty "Context" <\> concatWith (<\>) ctx)
    , nest 2 (pretty "Metacontext" <\> concatWith (<\>) subst')
    , pretty (prettyCallStack callStack)
    ]
    where
    (_, printCtx, ctx) = foldl' combine (0, Nil, Nil) (elems context)
    subst' = map (\ (m :=: v ::: _T) -> getPrint (ann (Print.meta m <+> pretty '=' <+> maybe (pretty '?') (printType opts printCtx) v ::: printType opts printCtx _T))) (metas subst)
  combine (d, print, ctx) (Binding n m _T) =
    let n' = intro n d
    in  ( succ d
        , print :> n'
        , ctx  :> getPrint (ann (n' ::: mult m (printType opts print _T))) )
  mult m = if
    | m == zero -> (pretty "0" <+>)
    | m == one  -> (pretty "1" <+>)
    | otherwise -> id


printErrReason :: Options -> Snoc Print -> ErrReason -> Doc Style
printErrReason opts ctx = group . \case
  FreeVariable n         -> fillSep [reflow "variable not in scope:", pretty n]
  AmbiguousName n qs     -> fillSep [reflow "ambiguous name", pretty n] <\> nest 2 (reflow "alternatives:" <\> unlines (map pretty qs))
  CouldNotSynthesize msg -> reflow "could not synthesize a type for" <> softline <> reflow msg
  ResourceMismatch n e a -> fillSep [reflow "uses of variable", pretty n, reflow "didn’t match requirements"]
    <> hardline <> pretty "expected:" <+> prettyQ e
    <> hardline <> pretty "  actual:" <+> prettyQ a
    where
    prettyQ = \case
      Zero -> pretty "0"
      One  -> pretty "1"
      Many -> pretty "arbitrarily many"
  Mismatch msg exp act   -> reflow msg
    <> hardline <> pretty "expected:" <> print exp'
    <> hardline <> pretty "  actual:" <> print act'
    where
    exp' = either reflow (getPrint . printType opts ctx) exp
    act' = getPrint (printType opts ctx act)
    -- line things up nicely for e.g. wrapped function types
    print = nest 2 . (flatAlt (line <> stimes (3 :: Int) space) mempty <>)
  Hole n _T              ->
    let _T' = getPrint (printType opts ctx _T)
    in fillSep [ reflow "found hole", pretty n, colon, _T' ]
  Invariant s -> reflow s


rethrowElabWarnings :: L.WriteC (Notice (Doc Style)) Warn m a -> m a
rethrowElabWarnings = L.runWrite inject
  where
  inject Elab.Warn{ source, reason } = Notice.Notice (Just Notice.Warn) [source] (printWarnReason reason) []

printWarnReason :: WarnReason -> Doc Style
printWarnReason = \case
  RedundantCatchAll n -> fillSep [reflow "redundant catch all pattern", pretty n]
  RedundantVariable n -> fillSep [reflow "redundant variable", pretty n]
