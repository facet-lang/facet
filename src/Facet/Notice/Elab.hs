{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
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
  let reason' = printReason context reason
  in Notice (Just Error) (slice src span) reason'
    [ getPrint $ printContextEntry l (n ::: foldCValue explicit Nil _T)
    | (l, n ::: _T) <- zip [N.Level 0..] (toList (elems context))
    ]
    -- FIXME: foldl over the context printing each element in the smaller context before it.


printReason :: Context Type -> Reason -> Doc [SGR]
printReason ctx = group . \case
  FreeVariable n         -> fillSep [reflow "variable not in scope:", pretty n]
  CouldNotSynthesize msg -> reflow "could not synthesize a type for" <> softline <> reflow msg
  Mismatch msg exp act   ->
    let exp' = either reflow (printType Nil) exp
        act' = printType Nil act
    in reflow msg
      </> pretty "expected:" <> print exp'
      </> pretty "  actual:" <> print act'
    where
    -- line things up nicely for e.g. wrapped function types
    print = nest 2 . (flatAlt (line <> stimes (3 :: Int) space) mempty <>)
  Hole n _T              ->
    let _T' = printType Nil _T
    in fillSep [reflow "found hole", pretty n, colon, _T' ]
  BadContext n           -> fillSep [ reflow "no variable bound for index", pretty (N.getIndex n), reflow "in context of length", pretty (length ctx) ]
  where
  -- FIXME: foldl over the context printing each element in the smaller context before it.
  env = elems ctx


printType :: Stack Print -> Type -> Doc [SGR]
printType env = getPrint . foldCValue explicit env
