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
import           Facet.Print
import           Facet.Source
import           Facet.Stack
import           Facet.Syntax
import           Silkscreen

-- Elaboration

rethrowElabErrors :: Source -> L.ThrowC (Notice [SGR]) Err m a -> m a
rethrowElabErrors src = L.runThrow $ \ Err{ span, reason, context } ->
  let (_, _, printCtx, ctx) = foldl combine (N.Level 0, Nil, Nil, Nil) (elems context)
  in Notice (Just Error) (slice src span) (printReason printCtx reason)
    (map (\ (l, s, e) -> getPrint (printContextEntry l (s == STerm) e)) (toList ctx))
  where
  combine (d, sort, print, ctx) (n ::: _T) =
    let entry = foldCValue explicit print _T
        s = sortOf sort _T
    in  ( succ d
        , sort :> s
        , print :> entry, ctx :> (d, s, n ::: entry) )


printReason :: Stack Print -> Reason -> Doc [SGR]
printReason ctx = group . \case
  FreeVariable m n       -> fillSep [reflow "variable not in scope:", maybe (pretty n) (pretty . (N.:.: n)) m]
  CouldNotSynthesize msg -> reflow "could not synthesize a type for" <> softline <> reflow msg
  Mismatch msg exp act   ->
    let exp' = either reflow (printType ctx) exp
        act' = printType ctx act
    in reflow msg
      </> pretty "expected:" <> print exp'
      </> pretty "  actual:" <> print act'
    where
    -- line things up nicely for e.g. wrapped function types
    print = nest 2 . (flatAlt (line <> stimes (3 :: Int) space) mempty <>)
  Hole n _T              ->
    let _T' = printType ctx _T
    in fillSep [reflow "found hole", pretty n, colon, _T' ]
  BadContext n           -> fillSep [ reflow "no variable bound for index", pretty (N.getIndex n), reflow "in context of length", pretty (length ctx) ]


printType :: Stack Print -> Type -> Doc [SGR]
printType env = getPrint . foldCValue explicit env
