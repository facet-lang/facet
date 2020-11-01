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
, forAll
, comp
, ($$)
, lam
, thunk
, string
  -- * Modules
, elabModule
, apply
, applyComp
  -- * Errors
, Err(..)
, Reason(..)
  -- * Machinery
, Elab(..)
, elab
, elabTele
, elabWith
, check
, Check(..)
, Synth(..)
) where

import           Control.Algebra
import           Control.Carrier.Error.Church
import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Effect.Empty
import           Control.Effect.Lens ((.=))
import           Control.Effect.Sum
import           Control.Lens (at, ix)
import           Control.Monad (unless, (<=<))
import           Data.Bifunctor (first)
import           Data.Foldable (foldl', for_, toList)
import qualified Data.IntMap as IntMap
import           Data.Maybe (catMaybes, fromMaybe)
import           Data.Semialign
import qualified Data.Set as Set
import           Data.Text (Text)
import           Data.Traversable (for, mapAccumL)
import           Data.Void
import           Facet.Context as Context
import           Facet.Core hiding (global, ($$))
import qualified Facet.Core as C
import           Facet.Effect.Time.System
import           Facet.Effect.Trace as Trace
import           Facet.Graph as Graph
import           Facet.Name hiding (L, R)
import           Facet.Span (Pos, Span(..))
import           Facet.Stack hiding ((!?))
import qualified Facet.Surface as S
import           Facet.Syntax
import           GHC.Stack
import           Prelude hiding (zipWith)

-- TODO:
-- - forcing
-- - thunks
-- - clause/pattern matrices
-- - tacit (eta-reduced) definitions w/ effects
-- - mutual recursion? does this work already? who knows
-- - datatypes containing computations

-- General

-- FIXME: we don’t get good source references during unification
unify :: Type -> Type -> Elab Type
unify = go
  where
  go t1 t2 = trace "unify" $ case t1 :===: t2 of
    VNe (Metavar v :$ Nil)  :===: x                       -> solve (v :=: x)
    x                       :===: VNe (Metavar v :$ Nil)  -> solve (v :=: x)
    -- FIXME: resolve globals to try to progress past certain inequalities
    VNe (h1 :$ e1)          :===: VNe (h2 :$ e2)          -> VNe . (h1 :$) <$ unless (h1 == h2) nope <*> unifySpine e1 e2
    VComp t1                :===: VComp t2                -> VComp <$> unifyComp t1 t2
    -- FIXME: these make me feel icky
    VComp (Comp Nothing t1) :===: t2                      -> go t1 t2
    t1                      :===: VComp (Comp Nothing t2) -> go t1 t2
    VNe{}                   :===: _                       -> nope
    VComp{}                 :===: _                       -> nope
    VType                   :===: VType                   -> pure VType
    VType                   :===: _                       -> nope
    VInterface              :===: VInterface              -> pure VInterface
    VInterface              :===: _                       -> nope
    VPrim p1                :===: VPrim p2                -> VPrim p1 <$ unless (p1 == p2) nope
    VPrim{}                 :===: _                       -> nope
    VCon{}                  :===: _                       -> nope
    VLam{}                  :===: _                       -> nope
    VOp{}                   :===: _                       -> nope
    where
    -- FIXME: build and display a diff of the root types
    nope = couldNotUnify "mismatch" t1 t2

    unifySpine sp1 sp2 = unless (length sp1 == length sp2) nope *> sequenceA (zipWith unifyArg sp1 sp2)
    unifyArg (p1, a1) (p2, a2) = (p1,) <$ unless (p1 == p2) nope <*> go a1 a2

  solve (n :=: val') = do
    subst <- get
    -- FIXME: occurs check
    case subst IntMap.! getMeta n of
      Just val ::: _T -> go val' val
      Nothing  ::: _T -> val' <$ put (insertSubst n (Just val' ::: _T) subst)

  unifyComp c1 c2 = case c1 :===: c2 of
    ForAll (Binding p1 n1 s1 t1) b1 :===: ForAll (Binding p2 _  s2 t2) b2 -> do
      unless (p1 == p2) nope
      s <- unifySig s1 s2
      t <- go t1 t2
      d <- asks @(Context Type) level
      let v = free d
      b <- unifyComp (b1 v) (b2 v)
      pure $ ForAll (Binding p1 n1 s t) (\ v -> bindComp d v b)
    Comp s1 t1      :===: Comp s2 t2      -> Comp <$> unifySig s1 s2 <*> go t1 t2
    Comp Nothing t1 :===: t2              -> fromValue <$> go t1 (VComp t2)
    t1              :===: Comp Nothing t2 -> fromValue <$> go (VComp t1) t2
    _               :===: _               -> nope
    where
    nope = couldNotUnify "mismatch" (VComp c1) (VComp c2)

    -- FIXME: unify the signatures
    unifySig s1 _ = pure s1
    -- unifySig s1 s2 = unless (length s1 == length s2) nope *> sequenceA (zipWith go s1 s2)


-- FIXME: should we give metas names so we can report holes or pattern variables cleanly?
meta :: Type -> Elab Meta
meta _T = do
  subst <- get
  let m = Meta (length subst)
  m <$ put (insertSubst m (Nothing ::: _T) subst)

-- FIXME: does instantiation need to be guided by the expected type?
-- FIXME: can implicits have effects? what do we do about the signature?
-- FIXME: can we avoid metas if we instantiate against a whole spine?
instantiate :: Expr ::: Comp -> Elab (Expr ::: Comp)
instantiate (e ::: _T) = case _T of
  ForAll (Binding Im _ _ _T) _B -> do
    m <- metavar <$> meta _T
    instantiate (e C.$$ (Im, m) ::: _B m)
  _                           -> pure $ e ::: _T


switch :: Synth a -> Check a
switch (Synth m) = Check $ trace "switch" . \ _K -> m >>= \ (a ::: _K') -> a <$ unify _K' _K

as :: Check a ::: Check Type -> Synth a
as (m ::: _T) = Synth $ do
  _T' <- check (_T ::: VType)
  a <- check (m ::: _T')
  pure $ a ::: _T'

resolveWith
  :: (forall sig m . Has Empty sig m => Module -> m (QName :=: Maybe Def ::: Comp))
  -> MQName
  -> Elab (QName :=: Maybe Def ::: Comp)
resolveWith lookup n = asks lookup >>= \case
  Just (n' :=: d ::: _T) -> pure $ n' :=: d ::: _T
  Nothing                -> do
    defs <- asks (foldMap (lookup . snd) . getGraph)
    case defs of
      []                -> freeVariable n
      [n' :=: d ::: _T] -> pure $ n' :=: d ::: _T
      -- FIXME: resolve ambiguities by type.
      _                 -> ambiguousName n (map (\ (q :=: _ ::: _) -> q) defs)

resolve :: Name -> Elab (QName :=: Maybe Def ::: Comp)
resolve n = resolveWith (lookupD n) (Nothing :? n)

resolveC :: Name -> Elab (QName :=: Maybe Def ::: Comp)
resolveC n = resolveWith (lookupC n) (Nothing :? n)

resolveQ :: QName -> Elab (QName :=: Maybe Def ::: Comp)
resolveQ q@(m :.: n) = lookupQ q <$> ask <*> ask >>= \case
  Just (q' :=: d ::: _T) -> pure $ q' :=: d ::: _T
  Nothing                -> freeVariable (Just m :? n)

resolveMD :: MQName -> Elab (QName :=: Maybe Def ::: Comp)
resolveMD (m :? n) = maybe (resolve n) (resolveQ . (:.: n)) m

-- FIXME: we’re instantiating when inspecting types in the REPL.
global :: QName ::: Comp -> Synth Value
global (q ::: _T) = Synth $ fmap VComp <$> instantiate (C.global q ::: _T)

lookupInContext :: Name -> Context Type -> Maybe (Level, Type)
lookupInContext = lookupLevel

lookupInSig :: MQName -> Module -> Graph -> [Value] -> Maybe (QName ::: Comp)
lookupInSig (m :? n) mod graph = matchWith $ \case
  VNe (Global q@(m':.:_) :$ _) -> do
    guard (maybe True (== m') m)
    (_ :=: Just (DInterface defs) ::: _) <- lookupQ q mod graph
    _T <- matchWith (\ (n' ::: _T) -> _T <$ guard (n' == n)) defs
    pure $ m':.:n ::: _T
  _                            -> Nothing

-- FIXME: do we need to instantiate here to deal with rank-n applications?
-- FIXME: effect ops not in the sig are reported as not in scope
-- FIXME: effect ops in the sig are available whether or not they’re in scope
var :: MQName -> Synth Value
var n@(m :? n') = Synth $ trace "var" $ ask >>= \ ctx -> case m of
  Nothing
    | Just (i, _T) <- lookupInContext n' ctx
    -> pure (free i ::: _T)
  _ -> do
    (mod, graph, sig) <- (,,) <$> ask <*> ask <*> ask
    case lookupInSig n mod graph sig of
      Just (n ::: _T) -> do
        n ::: _T <- instantiate (VOp (n :$ Nil) ::: _T)
        pure $ n ::: VComp _T
      _ -> do
        n :=: _ ::: _T <- resolveMD n
        synth $ global (n ::: _T)

hole :: Name -> Check a
hole n = Check $ \ _T -> err $ Hole n _T

($$) :: Synth Value -> Check Value -> Synth Value
f $$ a = Synth $ trace "$$" $ do
  f' ::: _F <- synth f
  -- FIXME: check that the signatures match
  (Binding _ _ delta _A, _B) <- expectQuantifier "in application" _F
  a' <- extendSig delta $ check (a ::: _A)
  pure $ f' C.$$ (Ex, a') ::: VComp (_B a')


elabBinder :: Has (Reader (Context Type)) sig m => (Value -> m Value) -> m (Value -> Value)
elabBinder b = do
  d <- asks @(Context Type) level
  b' <- b (free d)
  pure $ \ v -> C.bind d v b'

elabBinders :: (Traversable t, Has (Reader (Context Type)) sig m) => t (Name ::: Type) -> (t (Name ::: Type) -> m Value) -> m (t Type -> Value)
elabBinders p b = do
  d <- asks @(Context Type) level
  b' <- b p
  pure $ \ v -> binds (snd (foldl' (\ (d, s) v -> (succ d, IntMap.insert (getLevel d) v s)) (d, IntMap.empty) v)) b'

(|-) :: Has (Reader (Context Type)) sig m => Name ::: Type -> m a -> m a
t |- b = local @(Context Type) (|> t) b

infix 1 |-


-- Expressions

synthExpr :: HasCallStack => S.Ann (S.Expr Void) -> Synth Expr
synthExpr (S.Ann s _ e) = mapSynth (trace "synthExpr" . setSpan s) $ case e of
  S.Var n      -> var n
  S.Type       -> _Type
  S.TInterface -> _Interface
  S.TString    -> _String
  S.TComp t    -> VComp <$> elabSTelescope t
  S.App f a    -> synthExpr f $$ checkExpr a
  S.As t _T    -> as (checkExpr t ::: checkExpr _T)
  S.String s   -> string s
  S.Hole{}     -> nope
  S.Lam{}      -> nope
  S.Thunk{}    -> nope
  S.Force{}    -> nope
  S.M v        -> case v of {}
  where
  nope = Synth $ couldNotSynthesize (show e)

checkExpr :: HasCallStack => S.Ann (S.Expr Void) -> Check Expr
checkExpr expr@(S.Ann s _ e) = mapCheck (trace "checkExpr" . setSpan s) $ case e of
  S.Hole  n    -> hole n
  S.Lam cs     -> elabClauses cs
  S.Thunk e    -> thunk (checkExpr e)
  S.Force e    -> checkExpr e -- FIXME: this should convert between computation and value type
  S.Var{}      -> synth
  S.Type       -> synth
  S.TInterface -> synth
  S.TString    -> synth
  S.TComp{}    -> synth
  S.App{}      -> synth
  S.As{}       -> synth
  S.String{}   -> synth
  S.M v        -> case v of {}
  where
  synth = switch (synthExpr expr)


elabBinding :: S.Ann (S.Binding Void) -> [(Pos, Check Binding)]
elabBinding (S.Ann s _ (S.Binding p n d t)) =
  [ (start s, Check $ \ _T -> setSpan s . trace "elabBinding" $ do
    d' <- traverse (traverse (check . (::: VInterface) . elabSig)) d
    t' <- check (checkExpr t ::: _T)
    pure $ Binding p n d' t')
  | n <- maybe [Nothing] (map Just . toList) n ]

-- FIXME: synthesize the types of the operands against the type of the interface; this is a spine.
elabSig :: S.Ann (S.Interface Void) -> Check Value
elabSig (S.Ann s _ (S.Interface (S.Ann s' _ n) sp)) = Check $ \ _T -> setSpan s . trace "elabSig" $
  check (switch (foldl' ($$) (mapSynth (setSpan s') (var n)) (checkExpr <$> sp)) ::: _T)

elabSTelescope :: S.Ann (S.Comp Void) -> Synth Comp
elabSTelescope (S.Ann s _ (S.Comp bs d t)) = mapSynth (setSpan s . trace "elabSTelescope") $ foldr
  (\ (p, t) b -> mapSynth (setSpan (Span p (end s))) $ forAll t (\ v -> Check $ \ _T -> v |- check (switch b ::: _T)))
  (mapSynth (setSpan (foldr (flip (foldr ((<>) . S.ann))) (S.ann t) d)) (comp (map elabSig <$> d) (checkExpr t)))
  (elabBinding =<< bs)


_Type :: Synth Type
_Type = Synth $ pure $ VType ::: VType

_Interface :: Synth Type
_Interface = Synth $ pure $ VInterface ::: VType

_String :: Synth Type
_String = Synth $ pure $ VPrim TString ::: VType


forAll :: Check Binding -> (Name ::: Type -> Check Comp) -> Synth Comp
forAll t b = Synth $ trace "forAll" $ do
  -- FIXME: should we check that the signature is empty?
  _T@Binding{ name, type' = _A } <- check (t ::: VType)
  d <- asks @(Context Type) level
  _B <- check (b (fromMaybe __ name ::: _A) ::: VType)
  pure $ ForAll _T (\ v -> bindComp d v _B) ::: VType

comp :: Maybe [Check Value] -> Check Type -> Synth Comp
comp s t = Synth $ trace "comp" $ do
  s' <- traverse (traverse (check . (::: VInterface))) s
  t' <- check (t ::: VType)
  pure $ Comp s' t' ::: VType


lam :: Name -> (Name ::: Type -> Check Expr) -> Check Expr
lam n b = Check $ \ _T -> trace "lam" $ do
  -- FIXME: error if the signature is non-empty; variable patterns don’t catch effects.
  (Binding pl _ _ _A, _B) <- expectQuantifier "when checking lambda" _T
  -- FIXME: extend the signature if _B v is a Comp.
  b' <- elabBinder $ \ v -> checkComp (b (n ::: _A) ::: _B v)
  pure $ VLam pl [Clause (PVar (n ::: _A)) (b' . unsafeUnPVar)]

thunk :: Check Expr -> Check Expr
thunk e = Check $ \case
  VComp (Comp s t)  -> extendSig s $ check (e ::: VComp (Comp s t))
  VComp _T@ForAll{} -> check (e ::: VComp _T)
  t                 -> check (e ::: t)


-- FIXME: go find the pattern matching matrix algorithm
elabClauses :: [S.Clause Void] -> Check Expr
elabClauses [S.Clause (S.Ann _ _ (S.PVar n)) b] = lam n $ \ v -> mapCheck (v |-) (checkExpr b)
elabClauses cs = Check $ \ _T -> do
  -- FIXME: use the signature to elaborate the pattern
  (Binding _ _ _ _A, _B) <- expectQuantifier "when checking clauses" _T
  d <- asks (level @Type)
  -- FIXME: I don’t see how this can be correct; the context will not hold a variable but rather a pattern of them.
  let _B' = _B (free d)
  cs' <- for cs $ \ (S.Clause p b) -> check
    (   elabPattern p (\ p' -> do
      Clause p' <$> elabBinders p' (foldr (|-) (checkComp (checkExpr b ::: _B'))))
    ::: _A)
  pure $ VLam Ex cs'


-- FIXME: check for unique variable names
elabPattern :: S.Ann (S.Pattern Void) -> (Pattern (Name ::: Type) -> Elab a) -> Check a
elabPattern (S.Ann s _ p) k = Check $ \ _A -> trace "elabPattern" $ setSpan s $ case p of
  S.PWildcard -> k (PVar (__ ::: _A))
  S.PVar n    -> k (PVar (n  ::: _A))
  S.PCon n ps -> do
    q :=: _ ::: _T' <- resolveC n
    _T'' <- inst _T'
    subpatterns _A _T'' ps $ \ ps' -> k (PCon (q :$ fromList ps'))
  -- FIXME: look up the effect in the signature
  S.PEff n ps v -> do
    -- let _ = lookupInSig
    q :=: _ ::: _T' <- resolveC n
    _T'' <- inst _T'
    -- FIXME: what should the type of the continuation be? [effect result type] -> [remainder of body type after this pattern]?
    subpatterns _A _T'' ps $ \ ps' -> k (PEff q (fromList ps') (v ::: VType)) -- FIXME: lies
  -- FIXME: warn if using PAll with an empty sig.
  S.PAll n -> k (PVar (n  ::: _A))
  where
  inst = \case
  -- FIXME: assert that the signature is empty
    ForAll (Binding Im _ _ _T) _B -> meta _T >>= inst . _B . metavar
    _T                            -> pure _T
  subpatterns _A = go
    where
    go _T' = \case
      []   -> \ k -> unify (VComp _T') _A *> k []
      p:ps -> \ k -> do
        -- FIXME: assert that the signature is empty
        (Binding _ _ _ _A, _B) <- expectQuantifier "when checking constructor pattern" (VComp _T')
        -- FIXME: is this right? should we use `free` instead? if so, what do we push onto the context?
        v <- metavar <$> meta _A
        check
          (   elabPattern p (\ p' -> go (_B v) ps (\ ps' -> k (p' : ps')))
          ::: _A)


string :: Text -> Synth Expr
string s = Synth $ pure $ VPrim (VString s) ::: VPrim TString


-- Declarations

elabDataDef
  :: Has (Reader Graph :+: Reader Module :+: Throw Err :+: Time Instant :+: Trace) sig m
  => QName ::: Comp
  -> [S.Ann (Name ::: S.Ann (S.Comp Void))]
  -> m [(Name, Decl)]
-- FIXME: check that all constructors return the datatype.
elabDataDef (mname :.: dname ::: _T) constructors = trace "elabDataDef" $ do
  cs <- for constructors $ runWithSpan $ \ (n ::: t) -> do
    c_T <- elabTele $ go (switch (elabSTelescope t)) _T
    pure $ n :=: con (mname :.: n) Nil c_T ::: c_T
  pure
    $ (dname, Decl (Just (DData cs)) _T)
    : map (\ (n :=: c ::: c_T) -> (n, Decl (Just (DTerm c)) c_T)) cs
  where
  go k = \case
    Comp _ _                     -> check (k ::: VType)
    -- FIXME: can sigs appear here?
    ForAll (Binding _ n s _T) _B -> do
      d <- asks @(Context Type) level
      _B' <- fromMaybe __ n ::: _T |- go k (_B (free d))
      pure $ ForAll (Binding Im n s _T) (\ v -> bindComp d v _B')
  con q fs = \case
    -- FIXME: can this use lam?
    ForAll (Binding p n _ _T) _B -> VLam p [Clause (PVar (fromMaybe __ n ::: _T)) (\ v -> let v' = unsafeUnPVar v in con q (fs :> v') (_B v'))]
    _T                           -> VCon (q :$ fs)

elabInterfaceDef
  :: Has (Reader Graph :+: Reader Module :+: Throw Err :+: Time Instant :+: Trace) sig m
  => Comp
  -> [S.Ann (Name ::: S.Ann (S.Comp Void))]
  -> m Decl
elabInterfaceDef _T constructors = trace "elabInterfaceDef" $ do
  cs <- for constructors $ runWithSpan $ \ (n ::: t) -> tracePretty n $
    (n :::) <$> elabTele (go (check (switch (elabSTelescope t) ::: VType)) _T)
  pure $ Decl (Just (DInterface cs)) _T
  where
  go k = \case
    -- FIXME: check that the interface is a member of the sig.
    Comp _ _                     -> k
    ForAll (Binding _ n s _T) _B -> do
      d <- asks @(Context Type) level
      _B' <- fromMaybe __ n ::: _T |- go k (_B (free d))
      pure $ ForAll (Binding Im n s _T) (\ v -> bindComp d v _B')

-- FIXME: add a parameter for the effect signature.
elabTermDef
  :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Throw Err :+: Time Instant :+: Trace) sig m)
  => Comp
  -> S.Ann (S.Expr Void)
  -> m Expr
elabTermDef _T expr = runReader (S.ann expr) $ trace "elabTermDef" $ elab $ go (checkExpr expr) _T
  where
  go k t = case t of
    -- FIXME: this doesn’t do what we want for tacit definitions, i.e. where _T is itself a telescope.
    -- FIXME: eta-expanding here doesn’t help either because it doesn’t change the way elaboration of the surface term occurs.
    Comp s _T                           -> extendSig s $ check (k ::: _T)
    -- we’ve exhausted the named parameters; the rest is up to the body.
    ForAll (Binding _ Nothing _ _T) _B  -> check (k ::: VComp t)
    -- FIXME: can this use lam?
    ForAll (Binding p (Just n) _ _T) _B -> do
      -- FIXME: use the sig… somehow…
      -- FIXME: should signatures end up in the context?
      b' <- elabBinder $ \ v -> n ::: _T |- go k (_B v)
      pure $ VLam p [Clause (PVar (n ::: _T)) (b' . unsafeUnPVar)]


-- Modules

elabModule
  :: (HasCallStack, Has (Reader Graph :+: Throw Err :+: Time Instant :+: Trace) sig m)
  => S.Ann (S.Module Void)
  -> m Module
elabModule (S.Ann s _ (S.Module mname is os ds)) = execState (Module mname [] os mempty) . runReader s $ tracePretty mname $ do
  let (importedNames, imports) = mapAccumL (\ names (S.Ann _ _ S.Import{ name }) -> (Set.insert name names, Import name)) Set.empty is
  imports_ .= imports

  local (`restrict` importedNames) $ do
    -- FIXME: maybe figure out the graph for mutual recursion?
    -- FIXME: check for redundant naming

    -- elaborate all the types first
    es <- trace "types" $ for ds $ \ (S.Ann _ _ (dname, S.Ann s _ (S.Decl tele def))) -> tracePretty dname $ setSpan s $ do
      _T <- runModule . elabTele $ check (switch (elabSTelescope tele) ::: VType)

      decls_.at dname .= Just (Decl Nothing _T)
      case def of
        S.DataDef cs -> do
          decls <- runModule $ elabDataDef (mname :.: dname ::: _T) cs
          Nothing <$ for_ decls (\ (dname, decl) -> decls_.at dname .= Just decl)

        S.InterfaceDef os -> do
          decl <- runModule $ elabInterfaceDef _T os
          Nothing <$ (decls_.at dname .= Just decl)

        S.TermDef t -> pure (Just (S.ann tele, dname, t ::: _T))

    -- then elaborate the terms
    trace "definitions" $ for_ (catMaybes es) $ \ (s, dname, t ::: _T) -> setSpan s $ tracePretty dname $ do
      t' <- runModule $ elabTermDef _T t
      decls_.ix dname .= Decl (Just (DTerm t')) _T


runSubstWith :: (Subst -> a -> m b) -> StateC Subst m a -> m b
runSubstWith with = runState with emptySubst

runContext :: ReaderC (Context Type) m a -> m a
runContext = runReader Context.empty

runSig :: ReaderC [Value] m a -> m a
runSig = runReader []

extendSig :: Has (Reader [Value]) sig m => Maybe [Value] -> m a -> m a
extendSig = maybe id (local . (++))

runModule :: Has (State Module) sig m => ReaderC Module m a -> m a
runModule m = do
  mod <- get
  runReader mod m


-- Errors

setSpan :: Has (Reader Span) sig m => Span -> m a -> m a
setSpan = local . const

runWithSpan :: (a -> ReaderC Span m b) -> S.Ann a -> m b
runWithSpan k (S.Ann s _ a) = runReader s (k a)


data Err = Err
  { span      :: Span
  , reason    :: Reason
  , context   :: Context Type
  , callStack :: Stack Message -- FIXME: keep source references for each message.
  }

data Reason
  = FreeVariable MQName
  -- FIXME: add source references for the imports, definition sites, and any re-exports.
  | AmbiguousName MQName [QName]
  | CouldNotSynthesize String
  | Mismatch String (Either String Type) Type
  | Hole Name Type


-- FIXME: apply the substitution before showing this to the user
err :: Reason -> Elab a
err reason = do
  span <- ask
  ctx <- ask
  callStack <- Trace.callStack
  throwError $ Err span reason ctx callStack

mismatch :: String -> Either String Type -> Type -> Elab a
mismatch msg exp act = err $ Mismatch msg exp act

couldNotUnify :: String -> Type -> Type -> Elab a
couldNotUnify msg t1 t2 = mismatch msg (Right t2) t1

couldNotSynthesize :: String -> Elab a
couldNotSynthesize = err . CouldNotSynthesize

freeVariable :: MQName -> Elab a
freeVariable n = err $ FreeVariable n

ambiguousName :: MQName -> [QName] -> Elab a
ambiguousName n qs = err $ AmbiguousName n qs


-- Patterns

expectMatch :: (Type -> Maybe out) -> String -> String -> Type -> Elab out
expectMatch pat exp s _T = maybe (mismatch s (Left exp) _T) pure (pat _T)

expectQuantifier :: String -> Type -> Elab (Binding, Type -> Comp)
expectQuantifier = expectMatch (\case{ ForAll t b -> pure (t, b) ; _ -> Nothing } <=< stripEmpty) "{_} -> _"

stripEmpty :: Type -> Maybe Comp
stripEmpty = \case
  VComp (Comp Nothing t) -> stripEmpty t
  VComp t                -> Just t
  _                      -> Nothing


-- Machinery

newtype Elab a = Elab { runElab :: forall sig m . Has (Reader (Context Type) :+: Reader Graph :+: Reader Module :+: Reader [Value] :+: Reader Span :+: State Subst :+: Throw Err :+: Trace) sig m => m a }

instance Functor Elab where
  fmap f (Elab m) = Elab (fmap f m)

instance Applicative Elab where
  pure a = Elab $ pure a
  Elab f <*> Elab a = Elab (f <*> a)

instance Monad Elab where
  Elab m >>= f = Elab $ m >>= runElab . f

instance Algebra (Reader (Context Type) :+: Reader Graph :+: Reader Module :+: Reader [Value] :+: Reader Span :+: State Subst :+: Throw Err :+: Trace) Elab where
  alg hdl sig ctx = case sig of
    L rctx                          -> Elab $ alg (runElab . hdl) (inj rctx)  ctx
    R (L graph)                     -> Elab $ alg (runElab . hdl) (inj graph) ctx
    R (R (L mod))                   -> Elab $ alg (runElab . hdl) (inj mod)   ctx
    R (R (R (L sig)))               -> Elab $ alg (runElab . hdl) (inj sig)   ctx
    R (R (R (R (L span))))          -> Elab $ alg (runElab . hdl) (inj span)  ctx
    R (R (R (R (R (L subst)))))     -> Elab $ alg (runElab . hdl) (inj subst) ctx
    R (R (R (R (R (R (L throw)))))) -> Elab $ alg (runElab . hdl) (inj throw) ctx
    R (R (R (R (R (R (R trace)))))) -> Elab $ alg (runElab . hdl) (inj trace) ctx

elab :: Has (Reader Graph :+: Reader Module :+: Reader Span :+: Throw Err :+: Time Instant :+: Trace) sig m => Elab Value -> m Value
elab = elabWith (fmap pure . apply)

elabTele :: Has (Reader Graph :+: Reader Module :+: Reader Span :+: Throw Err :+: Time Instant :+: Trace) sig m => Elab Comp -> m Comp
elabTele = elabWith (fmap pure . applyComp)

elabWith :: Has (Reader Graph :+: Reader Module :+: Reader Span :+: Throw Err :+: Time Instant :+: Trace) sig m => (Subst -> a -> m b) -> Elab a -> m b
elabWith f = runSubstWith f . runContext . runSig . runElab


check :: (Check a ::: Type) -> Elab a
check (m ::: _T) = trace "check" $ runCheck m _T

checkComp :: (Check a ::: Comp) -> Elab a
checkComp (m ::: _T) = trace "checkComp" $ case _T of
  Comp sig _T -> extendSig sig (runCheck m _T)
  _           -> runCheck m (VComp _T)

-- FIXME: it’d be pretty cool if this produced a witness for the satisfaction of the checked type.
newtype Check a = Check { runCheck :: Type -> Elab a }
  deriving (Functor) via ReaderC Type Elab

mapCheck :: (Elab a -> Elab b) -> Check a -> Check b
mapCheck f m = Check $ \ _T -> f (runCheck m _T)

newtype Synth a = Synth { synth :: Elab (a ::: Type) }

instance Functor Synth where
  fmap f (Synth m) = Synth (first f <$> m)

mapSynth :: (Elab (a ::: Type) -> Elab (b ::: Type)) -> Synth a -> Synth b
mapSynth f = Synth . f . synth
