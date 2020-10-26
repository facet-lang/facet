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

rethrowElabErrors :: Source -> L.ThrowC (Notice Style) Err m a -> m a
rethrowElabErrors src = L.runThrow $ \ Err{ span, reason, context, callStack } ->
  let (_, _, printCtx, ctx) = foldl combine (0, Nil, Nil, Nil) (elems context)
  in Notice.Notice (Just Error) (slice src span) (reAnnotate Code (printReason printCtx reason))
    [ nest 2 (pretty "Bindings" <\> concatWith (surround hardline) (toList ctx))
    , nest 2 (pretty "Trace" <\> concatWith (surround hardline) (toList callStack))
    ]
  where
  combine (d, sort, print, ctx) (n ::: _T) =
    let s = sortOf sort _T
        n' = name s n d
    in  ( succ d
        , sort  :> s
        , print :> n'
        , ctx   :> reAnnotate Code (getPrint (ann (n' ::: printValue print _T))) )
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
printType env = getPrint . printValue env
