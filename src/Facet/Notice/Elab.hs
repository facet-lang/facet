module Facet.Notice.Elab
( -- * Elaboration
  rethrowElabErrors
, rethrowElabWarnings
) where

import           Data.Foldable (foldl')
import           Data.Semigroup (stimes)
import qualified Facet.Carrier.Throw.Inject as L
import qualified Facet.Carrier.Write.Inject as L
import           Facet.Context (elems, toEnv)
import qualified Facet.Context as C
import           Facet.Elab as Elab
import qualified Facet.Env as Env
import           Facet.Functor.Synth
import           Facet.Interface (interfaces)
import           Facet.Name
import           Facet.Notice as Notice hiding (level)
import           Facet.Pattern
import           Facet.Pretty
import           Facet.Print as Print
import           Facet.Semiring (Few(..), one, zero)
import           Facet.Snoc
import           Facet.Style
import           Facet.Subst (metas)
import           Facet.Syntax hiding (ann)
import           Facet.Type.Norm (apply, free, metavar)
import           GHC.Stack (prettyCallStack)
import           Prelude hiding (print, unlines)
import           Silkscreen

-- Elaboration

rethrowElabErrors :: Applicative m => Options Print -> L.ThrowC (Notice (Doc Style)) Err m a -> m a
rethrowElabErrors opts = L.runThrow (pure . rethrow)
  where
  rethrow Err{ callStack, context, reason, sig, subst } = Notice.Notice (Just Error) [] (printErrReason opts mempty reason)
    [ nest 2 (pretty "Context" <\> concatWith (<\>) ctx)
    , nest 2 (pretty "Metacontext" <\> concatWith (<\>) subst')
    , nest 2 (pretty "Provided interfaces" <\> concatWith (<\>) sig')
    , pretty (prettyCallStack callStack)
    ]
    where
    (_, _, printCtx, ctx) = foldl' combine (0, Env.empty, Env.empty, Nil) (elems context)
    subst' = map (\ (m :=: v) -> getPrint (Print.meta m <+> pretty '=' <+> maybe (pretty '?') (print opts printCtx) v)) (metas subst)
    sig' = getPrint . print opts printCtx . fmap (apply subst (toEnv context)) <$> (interfaces =<< sig)
    combine (d, env, prints, ctx) (C.Kind (n :==> _K)) =
      ( succ d
      , env Env.|> PVar (n :=: free (LName d n))
      , prints Env.|> PVar (n :=: intro n d)
      , ctx :> getPrint (print opts prints (ann (intro n d ::: print opts prints _K))) )
    combine (d, env, prints, ctx) (C.Type m _ p) =
      ( succ d
      , env Env.|> ((\ (n :==> _T) -> n :=: free (LName d n)) <$> p)
      , prints Env.|> ((\ (n :==> _) -> n :=: intro n d) <$> p)
      , ctx :> getPrint (print opts prints ((\ (n :==> _T) -> ann (intro n d ::: mult m (print opts prints (apply subst env _T)))) <$> p)) )
  mult m
    | m == zero = (pretty "0" <+>)
    | m == one  = (pretty "1" <+>)
    | otherwise = id


printErrReason :: Options Print -> Env.Env Print -> ErrReason -> Doc Style
printErrReason opts ctx = group . \case
  FreeVariable n               -> fillSep [reflow "variable not in scope:", prettyQName n]
  AmbiguousName n              -> fillSep [reflow "ambiguous name", prettyQName n] -- <\> nest 2 (reflow "alternatives:" <\> unlines (map prettyQName qs))
  CouldNotSynthesize           -> reflow "could not synthesize a type; try a type annotation"
  ResourceMismatch n e a       -> fillSep [reflow "uses of variable", pretty n, reflow "didn’t match requirements"]
    <> hardline <> pretty "expected:" <+> prettyQ e
    <> hardline <> pretty "  actual:" <+> prettyQ a
    where
    prettyQ = \case
      Zero -> pretty "0"
      One  -> pretty "1"
      Many -> pretty "arbitrarily many"
  UnifyType r (Exp exp) (Act act) -> reason r
    <> hardline <> pretty "expected:" <> align exp'
    <> hardline <> pretty "  actual:" <> align act'
    where
    reason = \case
      Mismatch   -> pretty "mismatch"
      Occurs v t -> reflow "infinite type:" <+> getPrint (print opts ctx (metavar v)) <+> reflow "occurs in" <+> getPrint (print opts ctx t)
    exp' = either reflow (getPrint . print opts ctx) exp
    act' = getPrint (print opts ctx act)
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
