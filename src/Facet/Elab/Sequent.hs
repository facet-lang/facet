module Facet.Elab.Sequent
( -- * Variables
  globalS
, varS
) where

import Control.Effect.Reader
import Control.Effect.State
import Control.Effect.Throw
import Control.Effect.Writer
import Facet.Context (level)
import Facet.Elab (ElabContext, ErrReason, context_, freeVariable, instantiate, lookupInContext, resolveQ, use)
import Facet.Functor.Synth
import Facet.Graph
import Facet.Lens as Lens (views)
import Facet.Module
import Facet.Name
import Facet.Sequent.Class as SQ
import Facet.Subst
import Facet.Syntax hiding (context_)
import Facet.Type.Norm
import Facet.Usage

-- Variables

-- FIXME: we’re instantiating when inspecting types in the REPL.
globalS :: (Has (State (Subst Type)) sig m, SQ.Sequent t c d, Applicative i) => QName ::: Type -> m (i t :==> Type)
globalS (q ::: _T) = do
  v <- SQ.varA (Global q)
  (\ (v ::: _T) -> v :==> _T) <$> instantiate const (v ::: _T)

-- FIXME: do we need to instantiate here to deal with rank-n applications?
-- FIXME: effect ops not in the sig are reported as not in scope
-- FIXME: effect ops in the sig are available whether or not they’re in scope
varS :: (Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason) sig m, Has (Writer Usage) sig m, SQ.Sequent t c d, Applicative i) => QName -> m (i t :==> Type)
varS n = views context_ (lookupInContext n) >>= \case
  [(n', Right (q, _T))] -> do
    use n' q
    d <- views context_ level
    SQ.varA (Free (toLeveled d (ident n'))) ==> pure _T
  _                     -> resolveQ n >>= \case
    n :=: DTerm _ _T -> globalS (n ::: _T)
    _ :=: _          -> freeVariable n
