module Facet.Notice.Elab
( -- * Elaboration
  rethrowElabErrors
) where

import           Data.Foldable (toList)
import           Data.Semigroup (stimes)
import qualified Facet.Carrier.Throw.Inject as L
import           Facet.Context
import           Facet.Core (Sort(..), sortOf)
import           Facet.Elab as Elab
import qualified Facet.Name as N
import           Facet.Notice
import           Facet.Pretty
import           Facet.Print as Print hiding (Hole)
import           Facet.Source
import           Facet.Stack
import           Facet.Syntax
import           Prelude hiding (unlines)
import           Prettyprinter (reAnnotate)
import           Silkscreen

-- Elaboration

rethrowElabErrors :: Source -> (Print.Highlight -> other) -> L.ThrowC (Notice other) Err m a -> m a
rethrowElabErrors src mapAnn = L.runThrow $ \ Err{ span, reason, context } ->
  let (_, _, printCtx, ctx) = foldl combine (0, Nil, Nil, Nil) (elems context)
  in Notice (Just Error) (slice src span) (reAnnotate mapAnn (printReason printCtx reason)) (toList ctx)
  where
  combine (d, sort, print, ctx) (n ::: _T) =
    let s = sortOf sort _T
        n' = name s surface n d
    in  ( succ d
        , sort  :> s
        , print :> n'
        , ctx   :> reAnnotate mapAnn (getPrint (ann (n' ::: printValue surface print _T))) )
  name = \case
    STerm -> intro
    _     -> tintro


printReason :: Stack Print -> Reason -> Doc Print.Highlight
printReason ctx = group . \case
  FreeVariable m n       -> fillSep [reflow "variable not in scope:", prettyMaybeQual m n]
  AmbiguousName m n qs   -> fillSep [reflow "ambiguous name", prettyMaybeQual m n] <\> nest 2 (reflow "alternatives:" <\> unlines (map pretty qs))
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
  where
  prettyMaybeQual m n = maybe (pretty n) (pretty . (N.:.: n)) m


printType :: Stack Print -> Type -> Doc Print.Highlight
printType env = getPrint . printValue surface env
