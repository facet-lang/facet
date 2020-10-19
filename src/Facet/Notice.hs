{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
module Facet.Notice
( -- * Notices
  Notice(..)
, prettyNotice
  -- * Parse errors
, rethrowParseErrors
  -- * Elaboration
, rethrowElabErrors
) where

import qualified Control.Carrier.Parser.Church as Parse
import           Control.Effect.Parser.Notice hiding (prettyNotice)
import           Control.Effect.Parser.Source (Source, slice)
import           Data.Foldable (toList)
import           Data.Semigroup (stimes)
import           Facet.Algebra
import qualified Facet.Carrier.Throw.Inject as L
import           Facet.Context (Context(..))
import qualified Facet.Elab as Elab
import qualified Facet.Name as N
import           Facet.Pretty
import           Facet.Print
import           Facet.Stack
import           Facet.Syntax
import           Silkscreen

-- Notices

prettyNotice :: Notice [SGR] -> Doc [SGR]
prettyNotice = prettyNoticeWith sgrStyle


-- Parsing

rethrowParseErrors :: L.ThrowC (Notice [SGR]) (Source, Parse.Err) m a -> m a
rethrowParseErrors = L.runThrow (uncurry Parse.errToNotice)


-- Elaboration

rethrowElabErrors :: Source -> L.ThrowC (Notice [SGR]) Elab.Err m a -> m a
rethrowElabErrors src = L.runThrow $ \ Elab.Err{ Elab.span, Elab.reason, Elab.context } ->
  let reason' = printReason context reason
  in Notice (Just Error) (slice src span) reason'
    [ getPrint $ printContextEntry l (n ::: foldCValue explicit Nil _T)
    | (l, n ::: _T) <- zip [N.Level 0..] (toList (elems context))
    ]
    -- FIXME: foldl over the context printing each element in the smaller context before it.


printReason :: Context Elab.Type -> Elab.Reason -> Doc [SGR]
printReason ctx = group . \case
  Elab.FreeVariable n         -> fillSep [reflow "variable not in scope:", pretty n]
  Elab.CouldNotSynthesize msg -> reflow "could not synthesize a type for" <> softline <> reflow msg
  Elab.Mismatch msg exp act   ->
    let exp' = either reflow (printType Nil) exp
        act' = printType Nil act
    in reflow msg
      </> pretty "expected:" <> print exp'
      </> pretty "  actual:" <> print act'
    where
    -- line things up nicely for e.g. wrapped function types
    print = nest 2 . (flatAlt (line <> stimes (3 :: Int) space) mempty <>)
  Elab.Hole n _T              ->
    let _T' = printType Nil _T
    in fillSep [reflow "found hole", pretty n, colon, _T' ]
  Elab.BadContext n           -> fillSep [ reflow "no variable bound for index", pretty (N.getIndex n), reflow "in context of length", pretty (length ctx) ]
  where
  -- FIXME: foldl over the context printing each element in the smaller context before it.
  env = elems ctx


printType :: Stack Print -> Elab.Type -> Doc [SGR]
printType env = getPrint . foldCValue explicit env
