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
, force
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
import           Control.Applicative (Alternative)
import           Control.Carrier.Error.Church
import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Effect.Empty
import           Control.Effect.Lens ((.=))
import           Control.Effect.Sum
import           Control.Lens (at, ix)
import           Control.Monad (unless, when, (<=<))
import           Data.Bifunctor (first)
import           Data.Foldable (asum, foldl', for_, toList)
import qualified Data.IntMap as IntMap
import           Data.Maybe (catMaybes, fromMaybe)
import           Data.Semialign
import qualified Data.Set as Set
import           Data.Text (Text)
import           Data.Traversable (for, mapAccumL)
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
unify = unifyValue
  where
  unifyValue t1 t2 = trace "unify" $ case t1 :===: t2 of
    VNe (Metavar v1 :$ Nil) :===: VNe (Metavar v2 :$ Nil) -> if v1 == v2 then pure (metavar v1) else solve (v1 :=: metavar v2)
    VNe (Metavar v :$ Nil)  :===: x                       -> solve (v :=: x)
    x                       :===: VNe (Metavar v :$ Nil)  -> solve (v :=: x)
    -- FIXME: resolve globals to try to progress past certain inequalities
    VNe (h1 :$ e1)          :===: VNe (h2 :$ e2)          -> VNe . (h1 :$) <$ unless (h1 == h2) nope <*> unifySpine e1 e2
    TSusp t1                :===: TSusp t2                -> TSusp <$> unifyComp t1 t2
    -- FIXME: these make me feel icky
    TSusp (TRet Nothing t1) :===: t2                      -> unifyValue t1 t2
    t1                      :===: TSusp (TRet Nothing t2) -> unifyValue t1 t2
    VNe{}                   :===: _                       -> nope
    TSusp{}                 :===: _                       -> nope
    KType                   :===: KType                   -> pure KType
    KType                   :===: _                       -> nope
    KInterface              :===: KInterface              -> pure KInterface
    KInterface              :===: _                       -> nope
    ECon{}                  :===: _                       -> nope
    ELam{}                  :===: _                       -> nope
    TString                 :===: TString                 -> pure TString
    TString{}               :===: _                       -> nope
    EString s1              :===: EString s2              -> EString s1 <$ unless (s1 == s2) nope
    EString{}               :===: _                       -> nope
    EOp{}                   :===: _                       -> nope
    where
    -- FIXME: build and display a diff of the root types
    nope = couldNotUnify "mismatch" t1 t2

    unifySpine sp1 sp2 = unless (length sp1 == length sp2) nope *> sequenceA (zipWith unifyArg sp1 sp2)
    unifyArg (p1, a1) (p2, a2) = (p1,) <$ unless (p1 == p2) nope <*> unifyValue a1 a2

  unifyComp c1 c2 = case c1 :===: c2 of
    TForAll (Binding p1 n1 s1 t1) b1 :===: TForAll (Binding p2 _  s2 t2) b2 -> do
      unless (p1 == p2) nope
      s <- unifySig s1 s2
      t <- unifyValue t1 t2
      d <- asks @(Context Type) level
      let v = free d
      b <- unifyComp (b1 v) (b2 v)
      pure $ TForAll (Binding p1 n1 s t) (\ v -> bindComp d v b)
    TRet s1 t1      :===: TRet s2 t2      -> TRet <$> unifySig s1 s2 <*> unifyValue t1 t2
    TRet Nothing t1 :===: t2              -> fromValue <$> unifyValue t1 (TSusp t2)
    t1              :===: TRet Nothing t2 -> fromValue <$> unifyValue (TSusp t1) t2
    _               :===: _               -> nope
    where
    nope = couldNotUnify "mismatch" (TSusp c1) (TSusp c2)

    -- FIXME: unify the signatures
    unifySig s1 _ = pure s1
    -- unifySig Nothing Nothing     = pure Nothing
    -- unifySig (Just s1) (Just s2) = Just <$ unless (length s1 == length s2) nope <*> sequenceA (zipWith unifyValue s1 s2)
    -- unifySig _         _         = nope

  solve (n :=: val') = do
    subst <- get
    -- FIXME: occurs check
    when (n `occursIn` val')
      $ mismatch "infinite type" (Right (metavar n)) val'
    case subst IntMap.! getMeta n of
      Just val ::: _T -> unifyValue val' val
      Nothing  ::: _T -> val' <$ put (insertSubst n (Just val' ::: _T) subst)


-- FIXME: should we give metas names so we can report holes or pattern variables cleanly?
meta :: Type -> Elab Meta
meta _T = do
  subst <- get
  let m = Meta (length subst)
  m <$ put (insertSubst m (Nothing ::: _T) subst)

-- FIXME: does instantiation need to be guided by the expected type?
-- FIXME: can implicits have effects? what do we do about the signature?
-- FIXME: can we avoid metas if we instantiate against a whole spine?
instantiate :: Expr ::: Comp -> Elab (Expr ::: Type)
instantiate (e ::: _T) = case _T of
  TForAll (Binding Im _ _ _T) _B -> do
    m <- metavar <$> meta _T
    instantiate (e C.$$ (Im, m) ::: _B m)
  _                              -> pure $ e ::: TSusp _T


switch :: Synth a -> Check a
switch (Synth m) = Check $ trace "switch" . \ _K -> m >>= \ (a ::: _K') -> a <$ unify _K' _K

as :: Check a ::: Check Type -> Synth a
as (m ::: _T) = Synth $ do
  _T' <- check (_T ::: KType)
  a <- check (m ::: _T')
  pure $ a ::: _T'

resolveWith
  :: (forall m . Alternative m => Name -> Module -> m (Q Name :=: Maybe Def ::: Comp))
  -> Q Name
  -> Elab (Q Name :=: Maybe Def ::: Comp)
resolveWith lookup n = lookupWith lookup n <$> ask <*> ask >>= \case
  []  -> freeVariable n
  [v] -> pure v
  ds  -> ambiguousName n (map (\ (q :=: _ ::: _) -> q) ds)

resolveC :: Q Name -> Elab (Q Name :=: Maybe Def ::: Comp)
resolveC = resolveWith lookupC

resolveQ :: Q Name -> Elab (Q Name :=: Maybe Def ::: Comp)
resolveQ = resolveWith lookupD

-- FIXME: we’re instantiating when inspecting types in the REPL.
global :: Q Name ::: Comp -> Synth Value
global (q ::: _T) = Synth $ instantiate (C.global q ::: _T)

lookupInContext :: Q Name -> Context Type -> Maybe (Level, Type)
lookupInContext (m:.:n)
  | m == Nil  = lookupLevel n
  | otherwise = const Nothing

-- FIXME: probably we should instead look up the effect op globally, then check for membership in the sig
lookupInSig :: Q Name -> Module -> Graph -> [Value] -> Maybe (Q Name ::: Comp)
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
-- FIXME: effect ops should not generate their own signatures; they should take on the ambient signature so long as the operation is in the signature.
-- otherwise put, we should think of the signature as being like the context (an input altered during elaboration, not an output), and of the signature attached to a TRet as a sort of row-polymorphic constraint: [Foo] A really means [Foo|E] A, where E is the ambient signature. So we must /instantiate/ E to the ambient signature, and then check the predicate.
var :: Q Name -> Synth Value
var n = Synth $ trace "var" $ ask >>= \ ctx -> if
  | Just (i, _T) <- lookupInContext n ctx -> pure (free i ::: _T)
  | otherwise                             -> lookupInSig n <$> ask <*> ask <*> ask >>= \case
    Just (n ::: _T) -> do
      n ::: _T <- instantiate (EOp (n :$ Nil) ::: _T)
      pure $ n ::: _T
    _ -> do
      n :=: _ ::: _T <- resolveQ n
      synth $ global (n ::: _T)

hole :: Name -> Check a
hole n = Check $ \ _T -> err $ Hole n _T

($$) :: Synth Value -> Check Value -> Synth Value
f $$ a = Synth $ trace "$$" $ do
  f' ::: _F <- synth f
  (Binding _ _ s _A, _B) <- expectQuantifier "in application" _F
  a' <- extendSig s (check (a ::: _A))
  pure $ f' C.$$ (Ex, a') ::: TSusp (_B a')


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

synthExpr :: HasCallStack => S.Ann S.Expr -> Synth Expr
synthExpr (S.Ann s _ e) = mapSynth (trace "synthExpr" . setSpan s) $ case e of
  S.Var n      -> var n
  S.KType      -> _Type
  S.KInterface -> _Interface
  S.TString    -> _String
  S.TComp t    -> TSusp <$> elabSTelescope t
  S.App f a    -> synthExpr f $$ checkExpr a
  S.As t _T    -> as (checkExpr t ::: checkExpr _T)
  S.String s   -> string s
  S.Hole{}     -> nope
  S.Lam{}      -> nope
  S.Thunk{}    -> nope
  S.Force e    -> force (synthExpr e)
  where
  nope = Synth $ couldNotSynthesize (show e)

checkExpr :: HasCallStack => S.Ann S.Expr -> Check Expr
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


elabBinding :: S.Ann S.Binding -> [(Pos, Check Binding)]
elabBinding (S.Ann s _ (S.Binding p n d t)) =
  [ (start s, Check $ \ _T -> setSpan s . trace "elabBinding" $ do
    d' <- traverse (traverse (check . (::: KInterface) . elabSig)) d
    t' <- check (checkExpr t ::: _T)
    pure $ Binding p n d' t')
  | n <- maybe [Nothing] (map Just . toList) n ]

elabSig :: S.Ann S.Interface -> Check Value
elabSig (S.Ann s _ (S.Interface (S.Ann s' _ n) sp)) = Check $ \ _T -> setSpan s . trace "elabSig" $
  check (switch (foldl' ($$) (mapSynth (setSpan s') (var n)) (checkExpr <$> sp)) ::: _T)

elabSTelescope :: S.Ann S.Comp -> Synth Comp
elabSTelescope (S.Ann s _ (S.Comp bs d t)) = mapSynth (setSpan s . trace "elabSTelescope") $ foldr
  (\ (p, t) b -> mapSynth (setSpan (Span p (end s))) $ forAll t (\ v -> mapCheck (v |-) (switch b)))
  (mapSynth (setSpan (foldr (flip (foldr ((<>) . S.ann))) (S.ann t) d)) (comp (map elabSig <$> d) (checkExpr t)))
  (elabBinding =<< bs)


_Type :: Synth Type
_Type = Synth $ pure $ KType ::: KType

_Interface :: Synth Type
_Interface = Synth $ pure $ KInterface ::: KType

_String :: Synth Type
_String = Synth $ pure $ TString ::: KType


forAll :: Check Binding -> (Name ::: Type -> Check Comp) -> Synth Comp
forAll t b = Synth $ trace "forAll" $ do
  -- FIXME: should we check that the signature is empty?
  _T@Binding{ name, type' = _A } <- check (t ::: KType)
  d <- asks @(Context Type) level
  _B <- check (b (fromMaybe __ name ::: _A) ::: KType)
  pure $ TForAll _T (\ v -> bindComp d v _B) ::: KType

comp :: Maybe [Check Value] -> Check Type -> Synth Comp
comp s t = Synth $ trace "comp" $ do
  s' <- traverse (traverse (check . (::: KInterface))) s
  t' <- check (t ::: KType)
  pure $ TRet s' t' ::: KType


lam :: Name -> (Name ::: Type -> Check Expr) -> Check Expr
lam n b = Check $ \ _T -> trace "lam" $ do
  -- FIXME: error if the signature is non-empty; variable patterns don’t catch effects.
  (Binding pl _ _s _A, _B) <- expectQuantifier "when checking lambda" _T
  -- FIXME: extend the signature if _B v is a Comp.
  b' <- elabBinder $ \ v -> check (b (n ::: _A) ::: TSusp (_B v))
  pure $ ELam pl [Clause (PVar (n ::: _A)) (b' . unsafeUnPVar)]

thunk :: Check Expr -> Check Expr
thunk e = Check $ trace "thunk" . \case
  -- FIXME: pretty sure this is redundant
  -- TSusp (TRet s t) -> extendSig s $ check (e ::: t)
  t                -> check (e ::: t)

force :: Synth Expr -> Synth Expr
force e = Synth $ trace "force" $ do
  e' ::: _T <- synth e
  (_s, _T') <- expectRet "when forcing computation" _T
  pure $ e' ::: _T'


-- FIXME: go find the pattern matching matrix algorithm
elabClauses :: [S.Clause] -> Check Expr
elabClauses [S.Clause (S.Ann _ _ (S.PVal (S.Ann _ _ (S.PVar n)))) b] = lam n $ \ v -> mapCheck (v |-) (checkExpr b)
elabClauses cs = Check $ \ _T -> do
  -- FIXME: use the signature to elaborate the pattern
  (Binding _ _ s _A, _B) <- expectQuantifier "when checking clauses" _T
  d <- asks (level @Type)
  -- FIXME: I don’t see how this can be correct; the context will not hold a variable but rather a pattern of them.
  let _B' = TSusp $ _B (free d)
  cs' <- for cs $ \ (S.Clause p b) -> elabPattern (fromMaybe [] s) _A p (\ p' -> do
    Clause p' <$> elabBinders p' (foldr (|-) (check (checkExpr b ::: _B'))))
  pure $ ELam Ex cs'


-- FIXME: check for unique variable names
elabPattern :: [Value] -> Type -> S.Ann S.EffPattern -> (Pattern (Name ::: Type) -> Elab a) -> Elab a
elabPattern sig = go
  where
  go _A (S.Ann s _ p) k = trace "elabPattern" $ setSpan s $ case p of
    S.PVal p -> goVal _A p k
    S.PEff n ps v -> do
      mod <- ask
      graph <- ask
      case lookupInSig n mod graph sig of
        Just (q ::: _T') -> do
          _T'' <- inst _T'
          subpatterns _T'' ps $ \ _T ps' -> k (PEff q (fromList ps') (v ::: TSusp (TForAll (Binding Ex Nothing Nothing _T) (const (TRet Nothing _A)))))
        _                -> freeVariable n
    -- FIXME: warn if using PAll with an empty sig.
    S.PAll n -> k (PVar (n  ::: _A))

  goVal _A (S.Ann s _ p) k = setSpan s $ case p of
    S.PWildcard -> k (PVar (__ ::: _A))
    S.PVar n    -> k (PVar (n  ::: _A))
    S.PCon n ps -> do
      q :=: _ ::: _T' <- resolveC n
      _T'' <- inst _T'
      subpatterns _T'' ps $ \ _T ps' -> unify _T _A *> k (PCon (q :$ fromList ps'))

  inst = \case
  -- FIXME: assert that the signature is empty
    TForAll (Binding Im _ _s _T) _B -> meta _T >>= inst . _B . metavar
    _T                              -> pure (TSusp _T)
  subpatterns _T' = \case
    []   -> \ k -> k _T' []
    p:ps -> \ k -> do
      -- FIXME: assert that the signature is empty
      (Binding _ _ _s _A, _B) <- expectQuantifier "when checking constructor pattern" _T'
      -- FIXME: is this right? should we use `free` instead? if so, what do we push onto the context?
      -- FIXME: I think this definitely isn’t right, as it instantiates variables which should remain polymorphic. We kind of need to open this existentially, I think?
      v <- metavar <$> meta _A
      goVal _A p (\ p' -> subpatterns (TSusp (_B v)) ps (\ _T ps' -> k _T (p' : ps')))


string :: Text -> Synth Expr
string s = Synth $ pure $ EString s ::: TString


-- Declarations

elabDataDef
  :: Has (Reader Graph :+: Reader MName :+: Reader Module :+: Throw Err :+: Time Instant :+: Trace) sig m
  => Q Name ::: Comp
  -> [S.Ann (Name ::: S.Ann S.Comp)]
  -> m [Name :=: Maybe Def ::: Comp]
-- FIXME: check that all constructors return the datatype.
elabDataDef (mname :.: dname ::: _T) constructors = trace "elabDataDef" $ do
  cs <- for constructors $ runWithSpan $ \ (n ::: t) -> do
    c_T <- elabTele $ go (switch (elabSTelescope t)) _T
    pure $ n :=: Just (DTerm (con (mname :.: n) Nil c_T)) ::: c_T
  pure
    $ (dname :=: Just (DData (scopeFromList cs)) ::: _T)
    : cs
  where
  go k = \case
    TRet _ _                     -> check (k ::: KType)
    -- FIXME: can sigs appear here?
    TForAll (Binding _ n s _T) _B -> do
      d <- asks @(Context Type) level
      _B' <- fromMaybe __ n ::: _T |- go k (_B (free d))
      pure $ TForAll (Binding Im n s _T) (\ v -> bindComp d v _B')
  con q fs = \case
    TForAll (Binding p n _s _T) _B -> ELam p [Clause (PVar (fromMaybe __ n ::: _T)) (\ v -> let v' = unsafeUnPVar v in con q (fs :> v') (_B v'))]
    _T                             -> ECon (q :$ fs)

elabInterfaceDef
  :: Has (Reader Graph :+: Reader MName :+: Reader Module :+: Throw Err :+: Time Instant :+: Trace) sig m
  => Comp
  -> [S.Ann (Name ::: S.Ann S.Comp)]
  -> m (Maybe Def ::: Comp)
elabInterfaceDef _T constructors = trace "elabInterfaceDef" $ do
  cs <- for constructors $ runWithSpan $ \ (n ::: t) -> tracePretty n $
    (\ _T -> n :=: Nothing ::: _T) <$> elabTele (go (check (switch (elabSTelescope t) ::: KType)) _T)
  pure $ Just (DInterface (scopeFromList cs)) ::: _T
  where
  go k = \case
    -- FIXME: check that the interface is a member of the sig.
    TRet _ _                     -> k
    TForAll (Binding _ n s _T) _B -> do
      d <- asks @(Context Type) level
      _B' <- fromMaybe __ n ::: _T |- go k (_B (free d))
      pure $ TForAll (Binding Im n s _T) (\ v -> bindComp d v _B')

-- FIXME: add a parameter for the effect signature.
elabTermDef
  :: (HasCallStack, Has (Reader Graph :+: Reader MName :+: Reader Module :+: Throw Err :+: Time Instant :+: Trace) sig m)
  => Comp
  -> S.Ann S.Expr
  -> m Expr
elabTermDef _T expr = runReader (S.ann expr) $ trace "elabTermDef" $ elab $ check (go (checkExpr expr) ::: TSusp _T)
  where
  go :: Check Expr -> Check Expr
  go k = Check $ \ _T -> case _T of
    TSusp (TForAll Binding{ name = Just n } _) -> check (lam n (\ v -> mapCheck (v |-) (go k)) ::: _T)
    -- FIXME: this doesn’t do what we want for tacit definitions, i.e. where _T is itself a telescope.
    -- FIXME: eta-expanding here doesn’t help either because it doesn’t change the way elaboration of the surface term occurs.
    -- we’ve exhausted the named parameters; the rest is up to the body.
    _                                          -> check (k ::: _T)


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
    es <- trace "types" $ for ds $ \ (S.Ann _ _ (dname, S.Ann s _ (S.Decl tele def))) -> tracePretty dname $ setSpan s $ do
      _T <- runModule . elabTele $ addEffectVar <$> check (switch (elabSTelescope tele) ::: KType)

      scope_.decls_.at dname .= Just (Nothing ::: _T)
      case def of
        S.DataDef cs -> do
          decls <- runModule $ elabDataDef (mname :.: dname ::: _T) cs
          Nothing <$ for_ decls (\ (dname :=: decl) -> scope_.decls_.at dname .= Just decl)

        S.InterfaceDef os -> do
          decl <- runModule $ elabInterfaceDef _T os
          Nothing <$ (scope_.decls_.at dname .= Just decl)

        S.TermDef t -> pure (Just (S.ann tele, dname, t ::: _T))

    -- then elaborate the terms
    trace "definitions" $ for_ (catMaybes es) $ \ (s, dname, t ::: _T) -> setSpan s $ tracePretty dname $ do
      t' <- runModule $ elabTermDef _T t
      scope_.decls_.ix dname .= (Just (DTerm t') ::: _T)


-- FIXME: do we need to shift levels internally? (how would levels be happening? this should be closed—but we certainly can’t /prove/ that it’s closed)
addEffectVar :: Comp -> Comp
addEffectVar _T = TForAll (Binding Im Nothing Nothing KInterface) (\ _E -> insertEffectVar _E _T)

insertEffectVar :: Type -> Comp -> Comp
insertEffectVar _E = go
  where
  go = \case
    TForAll b@Binding{ type' } _B -> TForAll b{ type' = case type' of { TSusp c -> TSusp (go c) ; t -> t } } (go . _B)
    TRet _ KType                  -> TRet Nothing KType
    TRet s t                      -> TRet (Just (maybe [_E] (_E:) s)) t


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
  = FreeVariable (Q Name)
  -- FIXME: add source references for the imports, definition sites, and any re-exports.
  | AmbiguousName (Q Name) [Q Name]
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

freeVariable :: Q Name -> Elab a
freeVariable n = err $ FreeVariable n

ambiguousName :: Q Name -> [Q Name] -> Elab a
ambiguousName n qs = err $ AmbiguousName n qs


-- Patterns

expectMatch :: (Type -> Maybe out) -> String -> String -> Type -> Elab out
expectMatch pat exp s _T = maybe (mismatch s (Left exp) _T) pure (pat _T)

expectQuantifier :: String -> Type -> Elab (Binding, Type -> Comp)
expectQuantifier = expectMatch (\case{ TForAll t b -> pure (t, b) ; _ -> Nothing } <=< stripEmpty) "{_} -> _"

stripEmpty :: Type -> Maybe Comp
stripEmpty = \case
  TSusp (TRet Nothing t) -> stripEmpty t
  TSusp t                -> Just t
  _                      -> Nothing

expectRet :: String -> Type -> Elab (Maybe [Value], Type)
expectRet = expectMatch (\case { TSusp (TRet s t) -> pure (s, t) ; _ -> Nothing }) "{_}"


-- Machinery

newtype Elab a = Elab { runElab :: forall sig m . Has (Reader (Context Type) :+: Reader Graph :+: Reader MName :+: Reader Module :+: Reader [Value] :+: Reader Span :+: State Subst :+: Throw Err :+: Trace) sig m => m a }

instance Functor Elab where
  fmap f (Elab m) = Elab (fmap f m)

instance Applicative Elab where
  pure a = Elab $ pure a
  Elab f <*> Elab a = Elab (f <*> a)

instance Monad Elab where
  Elab m >>= f = Elab $ m >>= runElab . f

instance Algebra (Reader (Context Type) :+: Reader Graph :+: Reader MName :+: Reader Module :+: Reader [Value] :+: Reader Span :+: State Subst :+: Throw Err :+: Trace) Elab where
  alg hdl sig ctx = case sig of
    L rctx                              -> Elab $ alg (runElab . hdl) (inj rctx)  ctx
    R (L graph)                         -> Elab $ alg (runElab . hdl) (inj graph) ctx
    R (R (L mname))                     -> Elab $ alg (runElab . hdl) (inj mname) ctx
    R (R (R (L mod)))                   -> Elab $ alg (runElab . hdl) (inj mod)   ctx
    R (R (R (R (L sig))))               -> Elab $ alg (runElab . hdl) (inj sig)   ctx
    R (R (R (R (R (L span)))))          -> Elab $ alg (runElab . hdl) (inj span)  ctx
    R (R (R (R (R (R (L subst))))))     -> Elab $ alg (runElab . hdl) (inj subst) ctx
    R (R (R (R (R (R (R (L throw))))))) -> Elab $ alg (runElab . hdl) (inj throw) ctx
    R (R (R (R (R (R (R (R trace))))))) -> Elab $ alg (runElab . hdl) (inj trace) ctx

elab :: Has (Reader Graph :+: Reader MName :+: Reader Module :+: Reader Span :+: Throw Err :+: Time Instant :+: Trace) sig m => Elab Value -> m Value
elab = elabWith (fmap pure . apply)

elabTele :: Has (Reader Graph :+: Reader MName :+: Reader Module :+: Reader Span :+: Throw Err :+: Time Instant :+: Trace) sig m => Elab Comp -> m Comp
elabTele = elabWith (fmap pure . applyComp)

elabWith :: Has (Reader Graph :+: Reader MName :+: Reader Module :+: Reader Span :+: Throw Err :+: Time Instant :+: Trace) sig m => (Subst -> a -> m b) -> Elab a -> m b
elabWith f = runSubstWith f . runContext . runSig . runElab


check :: (Check a ::: Type) -> Elab a
check (m ::: _T) = trace "check" $ case _T of
  TSusp (TRet sig _) -> extendSig sig (runCheck m _T)
  _                  -> runCheck m _T

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
