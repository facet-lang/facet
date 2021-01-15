{-# LANGUAGE OverloadedStrings #-}
-- | This module defines the /elaboration/ of terms in 'S.Expr' into values in 'Value'.
--
-- Elaboration is the only way 'Value's are constructed from untrusted terms, and so typechecking is performed at this point. If elaboration succeeds and a 'Value' is returned, that 'Value' does not require further verification; hence, 'Value's elide source span information.
module Facet.Elab
( -- * General
  unify
, switch
, as
, global
  -- * Expressions
, synthExpr
, checkExpr
, _Type
, ($$)
, lam
, thunk
, force
, string
  -- * Modules
, elabModule
  -- * Errors
, Err(..)
, Reason(..)
  -- * Unification
, ElabContext(..)
  -- * Machinery
, Elab(..)
, elab
, check
, Check(..)
, Synth(..)
) where

import           Control.Algebra
import           Control.Applicative (Alternative)
import           Control.Carrier.Error.Church
import           Control.Carrier.Fresh.Church
import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Effect.Empty
import           Control.Effect.Lens (view, (.=))
import           Control.Lens (Lens', at, ix, lens, set)
import           Control.Monad (unless)
import           Data.Bifunctor (first)
import           Data.Foldable (asum, foldl', for_, sequenceA_, toList)
import           Data.Maybe (catMaybes, fromMaybe)
import           Data.Semialign
import qualified Data.Set as Set
import           Data.Text (Text)
import           Data.Traversable (for, mapAccumL)
import           Facet.Carrier.Trace.Output as Trace
import           Facet.Context as Context
import           Facet.Core hiding (global, ($$))
import           Facet.Effect.Time.System
import           Facet.Graph as Graph
import           Facet.Lens
import           Facet.Name hiding (L, R)
import qualified Facet.Print as Print
import           Facet.Span (Pos, Span(..))
import           Facet.Stack
import qualified Facet.Surface as S
import           Facet.Syntax
import           GHC.Stack
import           Prelude hiding (span, zipWith)
import qualified Silkscreen

-- TODO:
-- - clause/pattern matrices
-- - tacit (eta-reduced) definitions w/ effects
-- - mutual recursion? does this work already? who knows
-- - datatypes containing computations
-- - separate the core elaborator language from the elaboration of surface terms

-- General

-- FIXME: should we give metas names so we can report holes or pattern variables cleanly?
meta :: Has (Fresh :+: State Context) sig m => (Maybe Value ::: Value) -> m Meta
meta (v ::: _T) = do
  m <- Meta <$> fresh
  m <$ modify (|> Flex m v _T)

-- FIXME: does instantiation need to be guided by the expected type?
-- FIXME: can implicits have effects? what do we do about the signature?
instantiate :: Has (Reader (Sig Value)) sig m => Quote ::: Value -> Elab m (Quote ::: Value)
instantiate (e ::: _T) = case _T of
  TForAll (Binding Im _ KInterface) _B -> do -- FIXME: this forces there to be exactly one effect var
    v <- askEffectVar
    d <- depth
    instantiate (QApp e (Im, quote d v) ::: _B v)
  TForAll (Binding Im _ _T) _B -> do
    m <- meta (Nothing ::: _T)
    instantiate (QApp e (Im, QVar (Metavar m)) ::: _B (metavar m))
  _                              -> pure $ e ::: _T


switch :: (HasCallStack, Has (Throw Err :+: Trace) sig m) => Synth m a -> Check m a
switch (Synth m) = Check $ trace "switch" . \ _K -> m >>= \ (a ::: _K') -> a <$ unify _K' _K

as :: Has Trace sig m => Check m Quote ::: Check m Quote -> Synth m Quote
as (m ::: _T) = Synth $ trace "as" $ do
  eval <- gets evalIn
  _T' <- eval <$> check (_T ::: KType)
  a <- check (m ::: _T')
  pure $ a ::: _T'

resolveWith
  :: Has (Throw Err :+: Trace) sig m
  => (forall m . Alternative m => Name -> Module -> m (Q Name :=: Maybe Def ::: Value))
  -> Q Name
  -> Elab m (Q Name :=: Maybe Def ::: Value)
resolveWith lookup n = asks (\ ElabContext{ module', graph } -> lookupWith lookup n module' graph) >>= \case
  []  -> freeVariable n
  [v] -> pure v
  ds  -> ambiguousName n (map (\ (q :=: _ ::: _) -> q) ds)

resolveC :: Has (Throw Err :+: Trace) sig m => Q Name -> Elab m (Q Name :=: Maybe Def ::: Value)
resolveC = resolveWith lookupC

resolveQ :: Has (Throw Err :+: Trace) sig m => Q Name -> Elab m (Q Name :=: Maybe Def ::: Value)
resolveQ = resolveWith lookupD

-- FIXME: we’re instantiating when inspecting types in the REPL.
global :: Has (Reader (Sig Value)) sig m => Q Name ::: Value -> Synth m Quote
global (q ::: _T) = Synth $ instantiate (QVar (Global q) ::: _T)

lookupInContext :: Q Name -> Context -> Maybe (Index, Value)
lookupInContext (m:.:n)
  | m == Nil  = lookupIndex n
  | otherwise = const Nothing

-- FIXME: probably we should instead look up the effect op globally, then check for membership in the sig
lookupInSig :: Q Name -> Module -> Graph -> [Value] -> Maybe (Q Name ::: Value)
lookupInSig (m :.: n) mod graph = fmap asum . fmap $ \case
  VNe (Global q@(m':.:_) :$ _) -> do
    guard (m == Nil || m == m')
    _ :=: Just (DInterface defs) ::: _ <- lookupQ q mod graph
    _ :=: _ ::: _T <- lookupScope n defs
    pure $ m':.:n ::: _T
  _                            -> Nothing

-- FIXME: do we need to instantiate here to deal with rank-n applications?
-- FIXME: effect ops not in the sig are reported as not in scope
-- FIXME: effect ops in the sig are available whether or not they’re in scope
var :: Has (Reader (Sig Value) :+: Throw Err :+: Trace) sig m => Q Name -> Synth m Quote
var n = Synth $ trace "var" $ get >>= \ ctx -> if
  | Just (i, _T) <- lookupInContext n ctx -> pure (QVar (Free i) ::: _T)
  | otherwise                             -> ask >>= \ sig -> asks (\ ElabContext{ module', graph } -> lookupInSig n module' graph (interfaces sig)) >>= \case
    Just (n ::: _T) -> instantiate (QEOp n ::: _T)
    _ -> do
      n :=: _ ::: _T <- resolveQ n
      synth $ global (n ::: _T)

hole :: Has (Throw Err :+: Trace) sig m => Name -> Check m a
hole n = Check $ \ _T -> err $ Hole n _T

($$) :: Has (Throw Err :+: Trace) sig m => Synth m Quote -> Check m Quote -> Synth m Quote
f $$ a = Synth $ trace "$$" $ do
  f' ::: _F <- synth f
  (Binding _ _ _A, _B) <- expectQuantifier "in application" _F
  a' <- check (a ::: _A)
  eval <- gets evalIn
  let a'' = eval a'
  pure $ QApp f' (Ex, a') ::: _B a''


(|-) :: (HasCallStack, Has Trace sig m) => Binding Value -> Elab m a -> Elab m a
-- FIXME: this isn’t _quite_ the shape we want to push onto the context because e.g. constructor patterns can bind multiple variables but they’d all have the same icit & signature.
-- FIXME: should this do something about the signature?
Binding _ n _T |- b = trace "|-" $ do
  i <- depth
  -- FIXME: should the context allow names in Maybe?
  modify (|> Rigid (fromMaybe __ n) _T)
  a <- b
  let extract (gamma :> Rigid{}) | i == level (Context gamma) = gamma
      extract (gamma :> e@Flex{})                             = extract gamma :> e
      extract (_     :> _)                                    = error "bad context entry"
      extract Nil                                             = error "bad context"
  a <$ modify (Context . extract . elems)

infix 1 |-


-- | Elaborate a type abstracted over another type’s parameters.
--
-- This is used to elaborate data constructors & effect operations, which receive the type/interface parameters as implicit parameters ahead of their own explicit ones.
abstract :: Has (Throw Err :+: Trace) sig m => Elab m Quote -> Value -> Elab m Quote
abstract body = go
  where
  go = \case
    TForAll t b -> do
      level <- depth
      b' <- t |- go (b (free level))
      pure $ QTForAll (quote level <$> set icit_ Im t) b'
    _           -> body


-- Expressions

synthExpr :: (HasCallStack, Has (Reader (Sig Value) :+: Throw Err :+: Trace) sig m) => S.Ann S.Expr -> Synth m Quote
synthExpr (S.Ann s _ e) = mapSynth (trace "synthExpr" . setSpan s) $ case e of
  S.Var n      -> var n
  S.KType      -> _Type
  S.KInterface -> _Interface
  S.TString    -> _String
  S.TComp t    -> elabComp t
  S.App f a    -> synthExpr f $$ checkExpr a
  S.As t _T    -> as (checkExpr t ::: checkExpr _T)
  S.String s   -> string s
  S.Hole{}     -> nope
  S.Lam{}      -> nope
  S.Thunk{}    -> nope
  S.Force e    -> force (synthExpr e)
  where
  nope = Synth $ couldNotSynthesize (show e)

checkExpr :: (HasCallStack, Has (Reader (Sig Value) :+: Throw Err :+: Trace) sig m) => S.Ann S.Expr -> Check m Quote
checkExpr expr@(S.Ann s _ e) = mapCheck (trace "checkExpr" . setSpan s) $ case e of
  S.Hole  n    -> hole n
  S.Lam cs     -> elabClauses cs
  S.Thunk e    -> thunk (checkExpr e)
  S.Force{}    -> synth
  S.Var{}      -> synth
  S.KType      -> synth
  S.KInterface -> synth
  S.TString    -> synth
  S.TComp{}    -> synth
  S.App{}      -> synth
  S.As{}       -> synth
  S.String{}   -> synth
  where
  synth = switch (synthExpr expr)


elabBinding :: (HasCallStack, Has (Reader (Sig Value) :+: Throw Err :+: Trace) sig m) => S.Ann S.Binding -> [(Pos, Check m (Binding Quote))]
elabBinding (S.Ann s _ (S.Binding p n d t)) =
  [ (start s, Check $ \ _T -> setSpan s . trace "elabBinding" $ do
    t' <- check (checkExpr t ::: _T)
    case d of
      Just d -> do
        d' <- traverse (check . (::: KInterface) . elabSig) d
        level <- depth
        e <- askEffectVar
        pure $ Binding p n (QTComp (Sig (quote level e) d') t')
      Nothing -> pure $ Binding p n t')
  | n <- maybe [Nothing] (map Just . toList) n ]

elabSig :: (HasCallStack, Has (Reader (Sig Value) :+: Throw Err :+: Trace) sig m) => S.Ann S.Interface -> Check m Quote
elabSig (S.Ann s _ (S.Interface (S.Ann s' _ n) sp)) = Check $ \ _T -> setSpan s . trace "elabSig" $
  check (switch (foldl' ($$) (mapSynth (setSpan s') (var n)) (checkExpr <$> sp)) ::: _T)

elabComp :: (HasCallStack, Has (Reader (Sig Value) :+: Throw Err :+: Trace) sig m) => S.Ann S.Comp -> Synth m Quote
elabComp (S.Ann s _ (S.Comp bs d b)) = Synth $ setSpan s . trace "elabComp" $ foldr
  (\ t b -> do
    t' <- check (snd t ::: KType)
    eval <- gets evalIn
    b' ::: _ <- fmap eval t' |- b
    pure $ QTForAll t' b' ::: KType)
  (do
    b' <- check (checkExpr b ::: KType)
    case d of
      Just d -> do
        d' <- traverse (check . (::: KInterface) . elabSig) d
        level <- depth
        e <- askEffectVar
        pure $ QTComp (Sig (quote level e) d') b' ::: KType
      Nothing -> pure (b' ::: KType))
  (elabBinding =<< bs)

-- comp type has a list of bindings, maybe a list of constraints, and a return type; turn the latter two into a QTComp and the former into a series of QTForAlls


_Type :: Synth m Quote
_Type = Synth $ pure $ QKType ::: KType

_Interface :: Synth m Quote
_Interface = Synth $ pure $ QKInterface ::: KType

_String :: Synth m Quote
_String = Synth $ pure $ QTString ::: KType


lam :: Has (Throw Err :+: Trace) sig m => Name -> Check m Quote -> Check m Quote
lam n b = Check $ \ _T -> trace "lam" $ do
  -- FIXME: error if the signature is non-empty; variable patterns don’t catch effects.
  (t@(Binding pl _ _A), _B) <- expectQuantifier "when checking lambda" _T
  -- FIXME: extend the signature if _B v is a TRet.
  d <- depth
  b' <- t{ name = Just n } |- check (b ::: _B (free d))
  pure $ QELam pl [(PVar n, b')]

thunk :: Has (Reader (Sig Value) :+: Throw Err :+: Trace) sig m => Check m a -> Check m a
thunk e = Check $ trace "thunk" . \case
  TComp (Sig _ s) t -> extendSig (Just s) $ check (e ::: t)
  t                 -> check (e ::: t)

force :: Has (Throw Err :+: Trace) sig m => Synth m a -> Synth m a
force e = Synth $ trace "force" $ do
  e' ::: _T <- synth e
  -- FIXME: should we check the signature? or can we rely on it already having been checked?
  (_s, _T') <- expectComp "when forcing computation" _T
  pure $ e' ::: _T'


-- FIXME: go find the pattern matching matrix algorithm
elabClauses :: (HasCallStack, Has (Reader (Sig Value) :+: Throw Err :+: Trace) sig m) => [S.Clause] -> Check m Quote
elabClauses [S.Clause (S.Ann _ _ (S.PVal (S.Ann _ _ (S.PVar n)))) b] = mapCheck (trace "elabClauses") $ lam n $ checkExpr b
elabClauses cs = Check $ \ _T -> trace "elabClauses" $ do
  -- FIXME: use the signature to elaborate the pattern
  (Binding _ _ _A, _B) <- expectQuantifier "when checking clauses" _T
  d <- depth
  -- FIXME: I don’t see how this can be correct; the context will not hold a variable but rather a pattern of them.
  let _B' = _B (free d)
  cs' <- for cs $ \ (S.Clause p b) -> elabPattern _A p (\ p' -> (tm <$> p',) <$> check (checkExpr b ::: _B'))
  pure $ QELam Ex cs'


-- FIXME: check for unique variable names
elabPattern :: Has (Reader (Sig Value) :+: Throw Err :+: Trace) sig m => Value -> S.Ann S.EffPattern -> (Pattern (Name ::: Value) -> Elab m a) -> Elab m a
elabPattern = go
  where
  go _A (S.Ann s _ p) k = trace "elabPattern" $ setSpan s $ case p of
    S.PVal p -> goVal _A p k
    S.PEff n ps v -> do
      ElabContext{ module' = mod, graph } <- ask
      (Sig _ sig, _A') <- expectComp "when elaborating pattern" _A
      case lookupInSig n mod graph sig of
        Just (q ::: _T') -> do
          _T'' <- inst _T'
          e <- askEffectVar
          subpatterns _T'' ps $ \ _T ps' -> let t = TForAll (Binding Ex Nothing _T) (const (TComp (Sig e sig) _A')) in Binding Ex (Just v) t |- k (PEff q (fromList ps') (v ::: t))
        _                -> freeVariable n
    -- FIXME: warn if using PAll with an empty sig.
    S.PAll n -> Binding Ex (Just n) _A |- k (PVar (n  ::: _A))

  goVal _A (S.Ann s _ p) k = setSpan s $ case p of
    S.PWildcard -> k (PVar (__ ::: _A))
    S.PVar n    -> Binding Ex (Just n) _A |- k (PVar (n  ::: _A))
    S.PCon n ps -> do
      q :=: _ ::: _T' <- resolveC n
      _T'' <- inst _T'
      subpatterns _T'' ps $ \ _T ps' -> unify _T _A *> k (PCon (q :$ fromList ps'))

  inst = \case
    TForAll (Binding Im _ _T) _B -> meta (Nothing ::: _T) >>= inst . _B . metavar
    _T                           -> pure _T
  subpatterns = flip $ foldr
    (\ p rest _A k -> do
      -- FIXME: assert that the signature is empty
      (Binding _ _ _A, _B) <- expectQuantifier "when checking constructor pattern" _A
      -- FIXME: is this right? should we use `free` instead? if so, what do we push onto the context?
      -- FIXME: I think this definitely isn’t right, as it instantiates variables which should remain polymorphic. We kind of need to open this existentially, I think?
      d <- depth
      goVal _A p (\ p' -> rest (_B (free d)) (\ _T ps' -> k _T (p' : ps'))))
      (\ _A k -> k _A [])


string :: Text -> Synth m Quote
string s = Synth $ pure $ QEString s ::: TString


-- Declarations

elabDataDef
  :: Has (Reader Graph :+: Reader MName :+: Reader Module :+: Throw Err :+: Time Instant :+: Trace) sig m
  => Name ::: Value
  -> [S.Ann (Name ::: S.Ann S.Comp)]
  -> m [Name :=: Maybe Def ::: Value]
-- FIXME: check that all constructors return the datatype.
elabDataDef (dname ::: _T) constructors = trace "elabDataDef" $ do
  mname <- ask
  cs <- for constructors $ runWithSpan $ \ (n ::: t) -> do
    c_T <- runReader (Sig (free (Level 0)) []) $ elab $ abstract (check (switch (elabComp t) ::: KType)) _T
    let c_T' = eval Nil mempty c_T
    pure $ n :=: Just (DTerm (con (mname :.: n) Nil c_T')) ::: c_T'
  pure
    $ (dname :=: Just (DData (scopeFromList cs)) ::: _T)
    : cs
  where
  con q fs = \case
    TForAll (Binding p n _T) _B -> ELam p [Clause (PVar (fromMaybe __ n)) (\ v -> let v' = unsafeUnPVar v in con q (fs :> v') (_B v'))]
    _T                          -> ECon (q :$ fs)

elabInterfaceDef
  :: Has (Reader Graph :+: Reader MName :+: Reader Module :+: Throw Err :+: Time Instant :+: Trace) sig m
  => Value
  -> [S.Ann (Name ::: S.Ann S.Comp)]
  -> m (Maybe Def ::: Value)
elabInterfaceDef _T constructors = trace "elabInterfaceDef" $ do
  cs <- for constructors $ runWithSpan $ \ (n ::: t) -> tracePretty n $ do
    _T' <- runReader (Sig (free (Level 0)) []) $ elab $ abstract (check (switch (elabComp t) ::: KType)) _T
    -- FIXME: check that the interface is a member of the sig.
    let _T'' = eval Nil mempty _T'
    pure $ n :=: Nothing ::: _T''
  pure $ Just (DInterface (scopeFromList cs)) ::: _T

-- FIXME: add a parameter for the effect signature.
elabTermDef
  :: (HasCallStack, Has (Reader Graph :+: Reader MName :+: Reader Module :+: Throw Err :+: Time Instant :+: Trace) sig m)
  => Value
  -> S.Ann S.Expr
  -> m Value
elabTermDef _T expr = runReader (S.ann expr) $ trace "elabTermDef" $ do
  runReader (Sig (free (Level 0)) []) $ elab $ Binding Im (Just (U "ε")) (free (Level 0)) |- eval Nil mempty <$> check (go (checkExpr expr) ::: _T)
  where
  go k = Check $ \ _T -> case _T of
    TForAll Binding{ name = Just n } _ -> tracePretty n $ check (lam n (go k) ::: _T)
    -- FIXME: this doesn’t do what we want for tacit definitions, i.e. where _T is itself a telescope.
    -- FIXME: eta-expanding here doesn’t help either because it doesn’t change the way elaboration of the surface term occurs.
    -- we’ve exhausted the named parameters; the rest is up to the body.
    _                                  -> check (k ::: _T)


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
      _T <- runModule $ runReader (Sig (free (Level 0)) []) $ elab $ eval Nil mempty <$> check (switch (elabComp tele) ::: KType)

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
    trace "definitions" $ for_ (catMaybes es) $ \ (s, dname, t ::: _T) -> local (const s) $ trace (Print.getPrint (Silkscreen.pretty dname Silkscreen.<+> Silkscreen.colon Silkscreen.<+> Print.printValue Nil _T)) $ do
      t' <- runModule $ elabTermDef _T t
      scope_.decls_.ix dname .= (Just (DTerm t') ::: _T)


extendSig :: Has (Reader (Sig Value)) sig m => Maybe [Value] -> m a -> m a
extendSig = maybe id (locally interfaces_ . (++))

askEffectVar :: Has (Reader (Sig Value)) sig m => m Value
askEffectVar = view effectVar_

depth :: Has (State Context) sig m => m Level
depth = gets level

runModule :: Has (State Module) sig m => ReaderC Module m a -> m a
runModule m = do
  mod <- get
  runReader mod m


-- Errors

setSpan :: Has (Reader ElabContext) sig m => Span -> m a -> m a
setSpan = locally span_ . const

runWithSpan :: (a -> ReaderC Span m b) -> S.Ann a -> m b
runWithSpan k (S.Ann s _ a) = runReader s (k a)


data Err = Err
  { span      :: Span
  , reason    :: Reason
  , context   :: Context
  , callStack :: Stack Message -- FIXME: keep source references for each message.
  }

data Reason
  = FreeVariable (Q Name)
  -- FIXME: add source references for the imports, definition sites, and any re-exports.
  | AmbiguousName (Q Name) [Q Name]
  | CouldNotSynthesize String
  | Mismatch String (Either String Value) Value
  | Hole Name Value
  | Invariant String


-- FIXME: apply the substitution before showing this to the user
err :: Has (Throw Err :+: Trace) sig m => Reason -> Elab m a
err reason = do
  ctx <- get
  span <- view span_
  callStack <- Trace.callStack
  throwError $ Err span reason ctx callStack

mismatch :: Has (Throw Err :+: Trace) sig m => String -> Either String Value -> Value -> Elab m a
mismatch msg exp act = err $ Mismatch msg exp act

couldNotUnify :: Has (Throw Err :+: Trace) sig m => String -> Value -> Value -> Elab m a
couldNotUnify msg t1 t2 = mismatch msg (Right t2) t1

couldNotSynthesize :: Has (Throw Err :+: Trace) sig m => String -> Elab m a
couldNotSynthesize = err . CouldNotSynthesize

freeVariable :: Has (Throw Err :+: Trace) sig m => Q Name -> Elab m a
freeVariable n = err $ FreeVariable n

ambiguousName :: Has (Throw Err :+: Trace) sig m => Q Name -> [Q Name] -> Elab m a
ambiguousName n qs = err $ AmbiguousName n qs


-- Patterns

expectMatch :: Has (Throw Err :+: Trace) sig m => (Value -> Maybe out) -> String -> String -> Value -> Elab m out
expectMatch pat exp s _T = maybe (mismatch s (Left exp) _T) pure (pat _T)

expectQuantifier :: Has (Throw Err :+: Trace) sig m => String -> Value -> Elab m (Binding Value, Value -> Value)
expectQuantifier = expectMatch (\case{ TForAll t b -> pure (t, b) ; _ -> Nothing }) "{_} -> _"

expectComp :: Has (Throw Err :+: Trace) sig m => String -> Value -> Elab m (Sig Value, Value)
expectComp = expectMatch (\case { TComp s t -> pure (s, t) ; _ -> Nothing }) "{_}"


-- Unification

data ElabContext = ElabContext
  { graph   :: Graph
  , mname   :: MName
  , module' :: Module
  , span    :: Span
  }

span_ :: Lens' ElabContext Span
span_ = lens (span :: ElabContext -> Span) (\ e span -> (e :: ElabContext){ span })


onTop :: (HasCallStack, Has (Throw Err :+: Trace) sig m) => (Level -> Meta :=: Maybe Value ::: Value -> Elab m (Maybe Suffix)) -> Elab m ()
onTop f = trace "onTop" $ do
  ctx <- get
  (gamma, elem) <- case elems ctx of
    gamma :> elem -> pure (Context gamma, elem)
    Nil           -> err $ Invariant "onTop in empty context"
  put gamma
  case elem of
    Flex n v _T -> f (level gamma) (n :=: v ::: _T) >>= \case
      Just v  -> modify (<>< v)
      Nothing -> modify (|> elem)
    _         -> onTop f <* modify (|> elem)

-- FIXME: we don’t get good source references during unification
unify :: (HasCallStack, Has (Throw Err :+: Trace) sig m) => Value -> Value -> Elab m ()
unify t1 t2 = trace "unify" $ value t1 t2
  where
  nope = couldNotUnify "mismatch" t1 t2

  value t1 t2 = trace "unify value" $ case (t1, t2) of
    (VNe (Metavar v1 :$ Nil), VNe (Metavar v2 :$ Nil)) -> trace "flex-flex" $ onTop $ \ _ (g :=: d ::: _K) -> case (g == v1, g == v2, d) of
      (True,  True,  _)       -> restore
      (True,  False, Nothing) -> replace [v1 :=: Just (metavar v2) ::: _K]
      (False, True,  Nothing) -> replace [v2 :=: Just (metavar v1) ::: _K]
      (True,  False, Just t)  -> value t (metavar v2) >> restore
      (False, True,  Just t)  -> value (metavar v1) t >> restore
      (False, False, _)       -> value (metavar v1) (metavar v2) >> restore
    (VNe (Metavar v1 :$ Nil), t2)                      -> solve v1 t2
    (t1, VNe (Metavar v2 :$ Nil))                      -> solve v2 t1
    (KType, KType)                                     -> pure ()
    (KType, _)                                         -> nope
    (KInterface, KInterface)                           -> pure ()
    (KInterface, _)                                    -> nope
    (TForAll t1 b1, TForAll t2 b2)                     -> do { binding t1 t2 ; d <- depth ; t1 |- value (b1 (free d)) (b2 (free d)) ; pure () }
    (TForAll{}, _)                                     -> nope
    (TComp s1 t1, TComp s2 t2)                         -> sig s1 s2 >> value t1 t2
    (TComp{}, _)                                       -> nope
    (ELam{}, ELam{})                                   -> nope
    (ELam{}, _)                                        -> nope
    (VNe (v1 :$ sp1), VNe (v2 :$ sp2))                 -> var v1 v2 >> spine (pl value) sp1 sp2
    (VNe{}, _)                                         -> nope
    (ECon (q1 :$ sp1), ECon (q2 :$ sp2))               -> unless (q1 == q2) nope >> spine value sp1 sp2
    (ECon{}, _)                                        -> nope
    (TString, TString)                                 -> pure ()
    (TString, _)                                       -> nope
    (EString e1, EString e2)                           -> unless (e1 == e2) nope
    (EString{}, _)                                     -> nope
    (EOp (q1 :$ sp1), EOp (q2 :$ sp2))                 -> unless (q1 == q2) nope >> spine (pl value) sp1 sp2
    (EOp{}, _)                                         -> nope

  var v1 v2 = trace "unify var" $ case (v1, v2) of
    (Global q1, Global q2)   -> unless (q1 == q2) nope
    (Global{}, _)            -> nope
    (Free v1, Free v2)       -> unless (v1 == v2) nope
    (Free{}, _)              -> nope
    (Metavar m1, Metavar m2) -> unless (m1 == m2) nope
    (Metavar{}, _)           -> nope

  pl f (p1, t1) (p2, t2) = unless (p1 == p2) nope >> f t1 t2

  spine f sp1 sp2 = trace "unify spine" $ unless (length sp1 == length sp2) nope >> sequenceA_ (zipWith f sp1 sp2)

  binding (Binding p1 _ t1) (Binding p2 _ t2) = trace "unify binding" $ unless (p1 == p2) nope >> value t1 t2

  sig (Sig e1 c1) (Sig e2 c2) = trace "unify sig" $ value e1 e2 >> spine value c1 c2

  solve v t = trace "solve" $ go []
    where
    go ext = onTop $ \ lvl (m :=: d ::: _K) -> case (m == v, occursIn (== Metavar m) lvl t, d) of
      (True,  True,  _)       -> mismatch "infinite type" (Right (metavar m)) t
      (True,  False, Nothing) -> replace (ext ++ [ m :=: Just t ::: _K ])
      (True,  False, Just t') -> modify (<>< ext) >> value t' t >> restore
      (False, True,  _)       -> go ((m :=: d ::: _K):ext) >> replace []
      (False, False, _)       -> go ext >> restore


-- Machinery

newtype Elab m a = Elab { runElab :: ReaderC ElabContext (StateC Context (FreshC m)) a }
  deriving (Algebra (Reader ElabContext :+: State Context :+: Fresh :+: sig), Applicative, Functor, Monad)

elab :: Has (Reader Graph :+: Reader MName :+: Reader Module :+: Reader Span :+: Throw Err :+: Time Instant :+: Trace) sig m => Elab m a -> m a
elab m = evalFresh 0 . evalState Context.empty $ do
  ctx <- mkContext
  runReader ctx . runElab $ m
  where
  mkContext = ElabContext <$> ask <*> ask <*> ask <*> ask


check :: Has Trace sig m => (Check m a ::: Value) -> Elab m a
check (m ::: _T) = trace "check" $ case _T of
  -- TSusp (TRet sig _) -> extendSig sig (runCheck m _T)
  _                  -> runCheck m _T

-- FIXME: it’d be pretty cool if this produced a witness for the satisfaction of the checked type.
newtype Check m a = Check { runCheck :: Value -> Elab m a }
  deriving (Functor) via ReaderC Value (Elab m)

mapCheck :: (Elab m a -> Elab m b) -> Check m a -> Check m b
mapCheck f m = Check $ \ _T -> f (runCheck m _T)

newtype Synth m a = Synth { synth :: Elab m (a ::: Value) }

instance Functor (Synth m) where
  fmap f (Synth m) = Synth (first f <$> m)

mapSynth :: (Elab m (a ::: Value) -> Elab m (b ::: Value)) -> Synth m a -> Synth m b
mapSynth f = Synth . f . synth
