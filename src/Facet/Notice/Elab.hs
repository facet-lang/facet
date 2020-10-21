module Facet.Notice.Elab
( -- * Notices
  Notice(..)
  -- * Elaboration
, rethrowElabErrors
) where

import           Data.Foldable (toList)
import           Data.Semigroup (stimes)
import           Facet.Algebra
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
import           Prettyprinter (reAnnotate)
import           Silkscreen

-- Elaboration

rethrowElabErrors :: Source -> (Print.Highlight -> other) -> L.ThrowC (Notice other) Err m a -> m a
rethrowElabErrors src mapAnn = L.runThrow $ \ Err{ span, reason, context } ->
  let (_, _, printCtx, ctx) = foldl combine (N.Level 0, Nil, Nil, Nil) (elems context)
  in Notice (Just Error) (slice src span) (reAnnotate mapAnn (printReason printCtx reason)) (toList ctx)
  where
  combine (d, sort, print, ctx) (n ::: _T) =
    let s = sortOf sort _T
        n' = name s explicit n d
    in  ( succ d
        , sort  :> s
        , print :> n'
        , ctx   :> reAnnotate mapAnn (getPrint (ann (n' ::: foldCValue explicit print _T))) )
  name = \case
    STerm -> intro
    _     -> tintro


printReason :: Stack Print -> Reason -> Doc Print.Highlight
printReason ctx = group . \case
  FreeVariable m n       -> fillSep [reflow "variable not in scope:", maybe (pretty n) (pretty . (N.:.: n)) m]
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
  BadContext n           -> fillSep [ reflow "no variable bound for index", pretty (N.getIndex n), reflow "in context of length", pretty (length ctx) ]


printType :: Stack Print -> Type -> Doc Print.Highlight
printType env = getPrint . foldCValue explicit env
