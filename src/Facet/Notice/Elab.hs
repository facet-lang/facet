module Facet.Notice.Elab
( -- * Elaboration
  rethrowElabErrors
, rethrowElabWarnings
) where

import           Data.Foldable (foldl')
import           Data.Semigroup (stimes)
import qualified Facet.Carrier.Throw.Inject as L
import qualified Facet.Carrier.Write.Inject as L
import           Facet.Context (elems)
import           Facet.Elab as Elab
import qualified Facet.Env as Env
import           Facet.Functor.Synth
import           Facet.Interface (interfaces)
import           Facet.Name
import           Facet.Notice as Notice hiding (level)
import           Facet.Pretty
import           Facet.Print as Print
import           Facet.Snoc
import           Facet.Style
import           Facet.Subst (metas)
import           Facet.Syntax hiding (ann)
import           Facet.Type.Norm (Type, apply, bound, metavar)
import           Facet.TypeContext (getTypeContext)
import           GHC.Stack (prettyCallStack)
import           Prelude hiding (print, unlines)
import           Silkscreen

-- Elaboration

rethrowElabErrors :: Applicative m => Options Print -> L.ThrowC (Notice (Doc Style)) Err m a -> m a
rethrowElabErrors opts = L.runThrow (pure . rethrow)
  where
  rethrow Err{ callStack, context, typeContext, reason, sig, subst } = Notice.Notice (Just Error) [] (printErrReason opts mempty reason)
    [ nest 2 (pretty "Context" <\> concatWith (<\>) ctx)
    , nest 2 (pretty "Type context" <\> concatWith (<\>) tyCtx)
    , nest 2 (pretty "Metacontext" <\> concatWith (<\>) subst')
    , nest 2 (pretty "Provided interfaces" <\> concatWith (<\>) sig')
    , pretty (prettyCallStack callStack)
    ]
    where
    (_, printCtx, ctx) = foldl' combine (0, Env.empty, Nil) (Env.bindings (elems context))
    (_, _, _, tyCtx) = foldl' combineTyCtx (0, Nil, Env.empty, Nil) (getTypeContext typeContext)
    subst' = map (\ (m :=: v) -> getPrint (Print.meta m <+> pretty '=' <+> maybe (pretty '?') (print opts printCtx) v)) (metas subst)
    sig' = getPrint . print opts printCtx . fmap (apply subst Nil) <$> (interfaces =<< sig)
    combineTyCtx
      :: Printable k
      => (Facet.Name.Level, Snoc (Name :=: Type), Env.Env Print, Snoc (Doc Style))
      -> Name :==> k
      -> (Facet.Name.Level, Snoc (Name :=: Type), Env.Env Print, Snoc (Doc Style))
    combineTyCtx (d, env, prints, ctx) (n :==> _K) =
      ( succ d
      , env :> (n :=: bound d)
      , prints Env.|> (n :=: intro n d)
      , ctx :> getPrint (print opts prints (ann (intro n d ::: print opts prints _K))) )
    combine (d, prints, ctx) (n :=: _T) =
      ( succ d
      , prints Env.|> (n :=: intro n d)
      , ctx :> getPrint (print opts prints (n :=: ann (intro n d ::: print opts prints (apply subst Nil _T)))) )


printErrReason :: Options Print -> Env.Env Print -> ErrReason -> Doc Style
printErrReason opts ctx = group . \case
  FreeVariable n               -> fillSep [reflow "variable not in scope:", pretty n]
  AmbiguousName n              -> fillSep [reflow "ambiguous name", pretty n] -- <\> nest 2 (reflow "alternatives:" <\> unlines (map prettyQName qs))
  CouldNotSynthesize           -> reflow "could not synthesize a type; try a type annotation"
  UnifyType r (Exp exp) (Act act) -> reason r
    <> hardline <> pretty "expected:" <> align exp'
    <> hardline <> pretty "  actual:" <> align act'
    where
    reason = \case
      Mismatch   -> pretty "mismatch"
      Occurs v t -> reflow "infinite type:" <+> getPrint (print opts ctx (metavar v)) <+> reflow "occurs in" <+> getPrint (print opts ctx t)
    exp' = either reflow (getPrint . print opts ctx) exp
    act' = either reflow (getPrint . print opts ctx) act
    -- line things up nicely for e.g. wrapped function types
    align = nest 2 . (flatAlt (line <> stimes (3 :: Int) space) mempty <>)
  UnifyKind (Exp exp) (Act act) -> pretty "mismatch"
    <> hardline <> pretty "expected:" <> align exp'
    <> hardline <> pretty "  actual:" <> align act'
    where
    exp' = either reflow (getPrint . print opts ctx) exp
    act' = getPrint (print opts ctx act)
    -- line things up nicely for e.g. wrapped function types
    align = nest 2 . (flatAlt (line <> stimes (3 :: Int) space) mempty <>)
  Hole n _T                    ->
    let _T' = getPrint (print opts ctx _T)
    in fillSep [ reflow "found hole", pretty n, colon, _T' ]
  Invariant s -> reflow s
  MissingInterface i -> reflow "could not find required interface" <+> getPrint (print opts ctx i)


rethrowElabWarnings :: L.WriteC (Notice (Doc Style)) Warn m a -> m a
rethrowElabWarnings = L.runWrite inject
  where
  inject Elab.Warn{ source, reason } = Notice.Notice (Just Notice.Warn) [source] (printWarnReason reason) []

printWarnReason :: WarnReason -> Doc Style
printWarnReason = \case
  RedundantCatchAll n -> fillSep [reflow "redundant catch all pattern", pretty n]
  RedundantVariable n -> fillSep [reflow "redundant variable", pretty n]
