module Facet.Notice.Elab
( -- * Elaboration
  rethrowElabErrors
) where

import           Data.Semigroup (stimes)
import qualified Facet.Carrier.Throw.Inject as L
import           Facet.Context
import           Facet.Core (Sort(..), Type, sortOf)
import           Facet.Elab as Elab
import           Facet.Notice as Notice
import           Facet.Pretty
import           Facet.Print as Print hiding (Hole)
import           Facet.Source
import           Facet.Stack
import           Facet.Style
import           Facet.Syntax
import           Prelude hiding (unlines)
import           Prettyprinter (reAnnotate)
import           Silkscreen

-- Elaboration

rethrowElabErrors :: Source -> L.ThrowC (Notice (Doc Style)) Err m a -> m a
rethrowElabErrors src = L.runThrow rethrow
  where
  rethrow Err{ span, reason, context, callStack } = Notice.Notice (Just Error) (Just (slice src span)) (reAnnotate Code (printReason printCtx reason))
    [ nest 2 (pretty "Context" <\> concatWith (<\>) ctx)
    , nest 2 (pretty "Trace" <\> concatWith (<\>) callStack)
    ]
    where
    (_, _, printCtx, ctx) = foldl combine (0, Nil, Nil, Nil) (elems context)
  combine (d, sort, print, ctx) (n :=: v ::: _T) =
    let s = sortOf sort _T
        n' = name s n d
    in  ( succ d
        , sort  :> s
        , print :> n'
        , ctx   :> reAnnotate Code (getPrint (ann (n' ::: printValue print _T))) <> case v of
          Nothing -> mempty
          Just v  -> space <> pretty '=' <+> reAnnotate Code (getPrint (printValue print v)) )
  name = \case
    STerm -> intro
    _     -> tintro


printReason :: Stack Print -> Reason -> Doc Print.Highlight
printReason ctx = group . \case
  FreeVariable n         -> fillSep [reflow "variable not in scope:", pretty n]
  AmbiguousName n qs     -> fillSep [reflow "ambiguous name", pretty n] <\> nest 2 (reflow "alternatives:" <\> unlines (map pretty qs))
  CouldNotSynthesize msg -> reflow "could not synthesize a type for" <> softline <> reflow msg
  Mismatch msg exp act   -> reflow msg
      <> hardline <> pretty "expected:" <> print exp'
      <> hardline <> pretty "  actual:" <> print act'
    where
    exp' = either reflow (printType ctx) exp
    act' = printType ctx act
    -- line things up nicely for e.g. wrapped function types
    print = nest 2 . (flatAlt (line <> stimes (3 :: Int) space) mempty <>)
  Hole n _T              ->
    let _T' = printType ctx _T
    in fillSep [reflow "found hole", pretty n, colon, _T' ]


printType :: Stack Print -> Type -> Doc Print.Highlight
printType env = getPrint . printValue env
