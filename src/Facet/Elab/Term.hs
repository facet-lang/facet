{-# LANGUAGE OverloadedStrings #-}
module Facet.Elab.Term
( -- * Terms
  global
, var
, tlam
, lam
, thunk
, force
, string
, synthExpr
, checkExpr
  -- * Declarations
, elabDataDef
, elabInterfaceDef
, elabTermDef
  -- * Modules
, elabModule
) where

import           Control.Algebra
import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Effect.Lens ((.=))
import           Control.Effect.Throw
import           Control.Lens (at, ix)
import           Data.Foldable
import           Data.Maybe (catMaybes)
import qualified Data.Set as Set
import           Data.Text (Text)
import           Data.Traversable (for, mapAccumL)
import           Facet.Core hiding (global)
import           Facet.Effect.Time.System
import           Facet.Effect.Trace
import           Facet.Elab
import           Facet.Elab.Type
import           Facet.Graph
import           Facet.Lens
import           Facet.Name
import qualified Facet.Print as Print
import           Facet.Span (Span(..))
import           Facet.Stack
import qualified Facet.Surface as S
import           Facet.Syntax
import           GHC.Stack
import qualified Silkscreen

-- FIXME: we’re instantiating when inspecting types in the REPL.
global :: Algebra sig m => Q Name ::: Type -> Synth m Expr
global (q ::: _T) = Synth $ instantiate XInst (XVar (Global q) ::: _T)

-- FIXME: do we need to instantiate here to deal with rank-n applications?
-- FIXME: effect ops not in the sig are reported as not in scope
-- FIXME: effect ops in the sig are available whether or not they’re in scope
var :: Has (Reader (Sig Type) :+: Throw Err :+: Trace) sig m => Q Name -> Synth m Expr
var n = Synth $ trace "var" $ get >>= \ ctx -> if
  | Just (i, _T) <- lookupInContext n ctx -> pure (XVar (Free i) ::: _T)
  | otherwise                             -> ask >>= \ sig -> asks (\ ElabContext{ module', graph } -> lookupInSig n module' graph (interfaces sig)) >>= \case
    Just (n ::: _T) -> instantiate XInst (XOp n ::: _T)
    _ -> do
      n :=: _ ::: _T <- resolveQ n
      synth $ global (n ::: _T)


tlam :: Has (Throw Err :+: Trace) sig m => Name -> Check m Expr -> Check m Expr
tlam n b = Check $ \ _T -> trace "tlam" $ do
  (_ ::: _A, _B) <- expectQuantifier "when checking type abstraction" _T
  d <- depth
  b' <- Just n ::: _A |- check (b ::: _B (free d))
  pure $ XTLam b'

lam :: Has (Throw Err :+: Trace) sig m => Name -> Check m Expr -> Check m Expr
lam n b = Check $ \ _T -> trace "lam" $ do
  (_ ::: _A, _B) <- expectFunction "when checking lambda" _T
  b' <- Just n ::: _A |- check (b ::: _B)
  pure $ XLam [(PVar n, b')]

thunk :: Has (Reader (Sig Type) :+: Throw Err :+: Trace) sig m => Check m a -> Check m a
thunk e = Check $ trace "thunk" . \case
  VTComp (Sig s) t -> extendSig (Just s) $ check (e ::: t)
  t                -> check (e ::: t)

force :: Has (Throw Err :+: Trace) sig m => Synth m a -> Synth m a
force e = Synth $ trace "force" $ do
  e' ::: _T <- synth e
  -- FIXME: should we check the signature? or can we rely on it already having been checked?
  (_s, _T') <- expectComp "when forcing computation" _T
  pure $ e' ::: _T'


-- FIXME: go find the pattern matching matrix algorithm
elabClauses :: (HasCallStack, Has (Reader (Sig Type) :+: Throw Err :+: Trace) sig m) => [S.Clause] -> Check m Expr
elabClauses [S.Clause (S.Ann _ _ (S.PVal (S.Ann _ _ (S.PVar n)))) b] = mapCheck (trace "elabClauses") $ lam n $ checkExpr b
elabClauses cs = Check $ \ _T -> trace "elabClauses" $ do
  -- FIXME: use the signature to elaborate the pattern
  (_ ::: _A, _B) <- expectFunction "when checking clauses" _T
  XLam <$> for cs (\ (S.Clause p b) -> elabPattern _A p (\ p' -> (tm <$> p',) <$> check (checkExpr b ::: _B)))


-- FIXME: check for unique variable names
elabPattern :: Has (Reader (Sig Type) :+: Throw Err :+: Trace) sig m => Type -> S.Ann S.EffPattern -> (Pattern (Name ::: Type) -> Elab m a) -> Elab m a
elabPattern = go
  where
  go _A (S.Ann s _ p) k = trace "elabPattern" $ setSpan s $ case p of
    S.PVal p -> goVal _A p k
    S.PEff n ps v -> do
      ElabContext{ module' = mod, graph } <- ask
      (Sig sig, _A') <- expectComp "when elaborating pattern" _A
      case lookupInSig n mod graph sig of
        Just (q ::: _T') -> do
          _T'' <- inst _T'
          subpatterns _T'' ps $ \ _T ps' -> let t = VTArrow (Nothing ::: _T) (VTComp (Sig sig) _A') in Just v ::: t |- k (PEff q (fromList ps') (v ::: t))
        _                -> freeVariable n
    -- FIXME: warn if using PAll with an empty sig.
    S.PAll n -> Just n ::: _A |- k (PVar (n  ::: _A))

  goVal _A (S.Ann s _ p) k = setSpan s $ case p of
    S.PWildcard -> k (PVar (__ ::: _A))
    S.PVar n    -> Just n ::: _A |- k (PVar (n  ::: _A))
    S.PCon n ps -> do
      q :=: _ ::: _T' <- resolveC n
      _T'' <- inst _T'
      subpatterns _T'' ps $ \ _T ps' -> unify _T _A *> k (PCon (q :$ fromList ps'))

  inst = \case
    VTForAll (_ ::: _T) _B -> meta (Nothing ::: _T) >>= inst . _B . metavar
    _T                     -> pure _T
  subpatterns = flip $ foldr
    (\ p rest _A k -> do
      -- FIXME: assert that the signature is empty
      (_ ::: _A, _B) <- expectFunction "when checking constructor pattern" _A
      -- FIXME: is this right? should we use `free` instead? if so, what do we push onto the context?
      -- FIXME: I think this definitely isn’t right, as it instantiates variables which should remain polymorphic. We kind of need to open this existentially, I think?
      goVal _A p (\ p' -> rest _B (\ _T ps' -> k _T (p' : ps'))))
      (\ _A k -> k _A [])


string :: Text -> Synth m Expr
string s = Synth $ pure $ XString s ::: VTString


synthExpr :: (HasCallStack, Has (Reader (Sig Type) :+: Throw Err :+: Trace) sig m) => S.Ann S.Expr -> Synth m Expr
synthExpr (S.Ann s _ e) = mapSynth (trace "synthExpr" . setSpan s) $ case e of
  S.Var n    -> var n
  S.App f a  -> app XApp (synthExpr f) (checkExpr a)
  S.As t _T  -> as (checkExpr t ::: checkType _T)
  S.String s -> string s
  S.Hole{}   -> nope
  S.Lam{}    -> nope
  S.Thunk{}  -> nope
  S.Force e  -> force (synthExpr e)
  where
  nope = Synth $ couldNotSynthesize (show e)

checkExpr :: (HasCallStack, Has (Reader (Sig Type) :+: Throw Err :+: Trace) sig m) => S.Ann S.Expr -> Check m Expr
checkExpr expr@(S.Ann s _ e) = mapCheck (trace "checkExpr" . setSpan s) $ case e of
  S.Hole  n  -> hole n
  S.Lam cs   -> elabClauses cs
  S.Thunk e  -> thunk (checkExpr e)
  S.Force{}  -> synth
  S.Var{}    -> synth
  S.App{}    -> synth
  S.As{}     -> synth
  S.String{} -> synth
  where
  synth = switch (synthExpr expr)


-- | Elaborate a type abstracted over another type’s parameters.
--
-- This is used to elaborate data constructors & effect operations, which receive the type/interface parameters as implicit parameters ahead of their own explicit ones.
abstract :: Has (Throw Err :+: Trace) sig m => Elab m TExpr -> Type -> Elab m TExpr
abstract body = go
  where
  go = \case
    VTForAll (     n ::: t) b -> do
      level <- depth
      b' <- Just n ::: t |- go (b (free level))
      pure $ TForAll (n ::: quote level t) b'
    VTArrow  (Just n ::: a) b -> do
      level <- depth
      b' <- Just n ::: a |- go b
      pure $ TForAll (n ::: quote level a) b'
    _                         -> body


-- Declarations

elabDataDef
  :: Has (Reader Graph :+: Reader MName :+: Reader Module :+: Throw Err :+: Time Instant :+: Trace) sig m
  => Name ::: Type
  -> [S.Ann (Name ::: S.Ann S.Type)]
  -> m [Name :=: Maybe Def ::: Type]
-- FIXME: check that all constructors return the datatype.
elabDataDef (dname ::: _T) constructors = trace "elabDataDef" $ do
  mname <- ask
  cs <- for constructors $ runWithSpan $ \ (n ::: t) -> do
    c_T <- elab $ abstract (check (checkType t ::: VKType)) _T
    let c_T' = eval Nil mempty c_T
    pure $ n :=: Just (DTerm (con (mname :.: n) c_T')) ::: c_T'
  pure
    $ (dname :=: Just (DData (scopeFromList cs)) ::: _T)
    : cs
  where
  con q = go Nil where
    go fs = \case
      -- FIXME: earlier indices should be shifted
      -- FIXME: XTLam is only for the type parameters
      -- type parameters presumably shouldn’t be represented in the elaborated data
      VTForAll (_ ::: _T) _B -> XTLam (go (fs :> XVar (Free (Index 0))) (_B (free (Level (length fs)))))
      _T                     -> XCon (q :$ fs)

elabInterfaceDef
  :: Has (Reader Graph :+: Reader MName :+: Reader Module :+: Throw Err :+: Time Instant :+: Trace) sig m
  => Type
  -> [S.Ann (Name ::: S.Ann S.Type)]
  -> m (Maybe Def ::: Type)
elabInterfaceDef _T constructors = trace "elabInterfaceDef" $ do
  cs <- for constructors $ runWithSpan $ \ (n ::: t) -> tracePretty n $ do
    _T' <- elab $ abstract (check (checkType t ::: VKType)) _T
    -- FIXME: check that the interface is a member of the sig.
    let _T'' = eval Nil mempty _T'
    pure $ n :=: Nothing ::: _T''
  pure $ Just (DInterface (scopeFromList cs)) ::: _T

-- FIXME: add a parameter for the effect signature.
elabTermDef
  :: (HasCallStack, Has (Reader Graph :+: Reader MName :+: Reader Module :+: Throw Err :+: Time Instant :+: Trace) sig m)
  => Type
  -> S.Ann S.Expr
  -> m Expr
elabTermDef _T expr = runReader (S.ann expr) $ trace "elabTermDef" $ do
  runReader (Sig @Type []) $ elab $ Just (U "ε") ::: free (Level 0) |- check (go (checkExpr expr) ::: _T)
  where
  go k = Check $ \ _T -> case _T of
    VTForAll (n ::: _) _     -> tracePretty n $ check (tlam n (go k) ::: _T)
    VTArrow (Just n ::: _) _ -> tracePretty n $ check (lam  n (go k) ::: _T)
    -- FIXME: this doesn’t do what we want for tacit definitions, i.e. where _T is itself a telescope.
    -- FIXME: eta-expanding here doesn’t help either because it doesn’t change the way elaboration of the surface term occurs.
    -- we’ve exhausted the named parameters; the rest is up to the body.
    _                        -> check (k ::: _T)

-- - we shouldn’t instantiate with the sig var
-- - we should unify sig vars in application rule (but not specialize thus)
-- - we should check if the sig var is actually being used and only use the function argument in that case
-- - factor types and expressions separately
-- elabWithSig :: (Expr -> Expr) -> m Expr
-- elabWithSig f = do
--   _


-- Modules

elabModule
  :: (HasCallStack, Has (Reader Graph :+: Throw Err :+: Time Instant :+: Trace) sig m)
  => S.Ann S.Module
  -> m Module
elabModule (S.Ann s _ (S.Module mname is os ds)) = execState (Module mname [] os mempty) . runReader mname . runReader s $ trace (prettyMName mname) $ do
  let (importedNames, imports) = mapAccumL (\ names (S.Ann _ _ S.Import{ name }) -> (Set.insert name names, Import name)) Set.empty is
  imports_ .= imports

  local (`restrict` importedNames) $ do
    -- FIXME: maybe figure out the graph for mutual recursion?
    -- FIXME: check for redundant naming

    -- elaborate all the types first
    es <- trace "types" $ for ds $ \ (S.Ann _ _ (dname, S.Ann s _ (S.Decl tele def))) -> tracePretty dname $ local (const s) $ do
      -- FIXME: add the effect var to the QComp before evaluating.
      _T <- runModule $ elab $ eval Nil mempty <$> check (checkType tele ::: VKType)

      scope_.decls_.at dname .= Just (Nothing ::: _T)
      case def of
        S.DataDef cs -> do
          decls <- runModule $ elabDataDef (dname ::: _T) cs
          Nothing <$ for_ decls (\ (dname :=: decl) -> scope_.decls_.at dname .= Just decl)

        S.InterfaceDef os -> do
          decl <- runModule $ elabInterfaceDef _T os
          Nothing <$ (scope_.decls_.at dname .= Just decl)

        S.TermDef t -> pure (Just (S.ann tele, dname, t ::: _T))

    -- then elaborate the terms
    trace "definitions" $ for_ (catMaybes es) $ \ (s, dname, t ::: _T) -> local (const s) $ trace (Print.getPrint (Silkscreen.pretty dname Silkscreen.<+> Silkscreen.colon Silkscreen.<+> Print.printType Nil _T)) $ do
      t' <- runModule $ elabTermDef _T t
      scope_.decls_.ix dname .= (Just (DTerm t') ::: _T)


-- Errors

expectQuantifier :: Has (Throw Err :+: Trace) sig m => String -> Type -> Elab m (Name ::: Type, Type -> Type)
expectQuantifier = expectMatch (\case{ VTForAll t b -> pure (t, b) ; _ -> Nothing }) "{_} -> _"

expectComp :: Has (Throw Err :+: Trace) sig m => String -> Type -> Elab m (Sig Type, Type)
expectComp = expectMatch (\case { VTComp s t -> pure (s, t) ; _ -> Nothing }) "{_}"


-- Elaboration

extendSig :: Has (Reader ElabContext) sig m => Maybe [Type] -> m a -> m a
extendSig = maybe id (locally (sig_.interfaces_) . (++))

runModule :: Has (State Module) sig m => ReaderC Module m a -> m a
runModule m = do
  mod <- get
  runReader mod m

runWithSpan :: (a -> ReaderC Span m b) -> S.Ann a -> m b
runWithSpan k (S.Ann s _ a) = runReader s (k a)
