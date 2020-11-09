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
  -- * Machinery
, ElabContext(..)
, sig_
, Elab(..)
, elab
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
import           Control.Effect.Lens (view, (.=))
import           Control.Effect.Sum
import           Control.Lens (Lens', at, ix, lens)
import           Control.Monad (unless, (<=<))
import           Data.Bifunctor (first)
import           Data.Foldable (asum, foldl', for_, toList)
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
import           Facet.Lens
import           Facet.Name hiding (L, R)
import           Facet.Span (Pos, Span(..))
import           Facet.Stack hiding ((!?))
import qualified Facet.Surface as S
import           Facet.Syntax
import           GHC.Stack
import           Prelude hiding (span, zipWith)

-- TODO:
-- - clause/pattern matrices
-- - tacit (eta-reduced) definitions w/ effects
-- - mutual recursion? does this work already? who knows
-- - datatypes containing computations
-- - separate the core elaborator language from the elaboration of surface terms

-- General

-- FIXME: should we give metas names so we can report holes or pattern variables cleanly?
meta :: Type -> Elab Level
meta _T = do
  ctx <- get
  level ctx <$ put (ctx |> Ty __ Nothing _T)

-- FIXME: does instantiation need to be guided by the expected type?
-- FIXME: can implicits have effects? what do we do about the signature?
instantiate :: Quote ::: Comp -> Elab (Quote ::: Type)
instantiate (e ::: _T) = case _T of
  TForAll (Binding Im _ _ _T) _B -> do
    m <- meta _T
    instantiate (QApp e (Im, QVar (Free (Index 0))) ::: _B (free m))
  _                              -> pure $ e ::: TSusp _T


switch :: Synth a -> Check a
switch (Synth m) = Check $ trace "switch" . \ _K -> m >>= \ (a ::: _K') -> a <$ unify _K' _K

as :: Check Quote ::: Check Quote -> Synth Quote
as (m ::: _T) = Synth $ trace "as" $ do
  env <- gets (fmap entryDef . elems)
  _T' <- eval env <$> check (_T ::: KType)
  a <- check (m ::: _T')
  pure $ a ::: _T'

resolveWith
  :: (forall m . Alternative m => Name -> Module -> m (Q Name :=: Maybe Def ::: Comp))
  -> Q Name
  -> Elab (Q Name :=: Maybe Def ::: Comp)
resolveWith lookup n = asks (\ ElabContext{ module', graph } -> lookupWith lookup n module' graph) >>= \case
  []  -> freeVariable n
  [v] -> pure v
  ds  -> ambiguousName n (map (\ (q :=: _ ::: _) -> q) ds)

resolveC :: Q Name -> Elab (Q Name :=: Maybe Def ::: Comp)
resolveC = resolveWith lookupC

resolveQ :: Q Name -> Elab (Q Name :=: Maybe Def ::: Comp)
resolveQ = resolveWith lookupD

-- FIXME: we’re instantiating when inspecting types in the REPL.
global :: Q Name ::: Comp -> Synth Quote
global (q ::: _T) = Synth $ instantiate (QVar (Global q) ::: _T)

lookupInContext :: Q Name -> Context -> Maybe (Index, Type)
lookupInContext (m:.:n)
  | m == Nil  = lookupIndex n
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
var :: Q Name -> Synth Quote
var n = Synth $ trace "var" $ get >>= \ ctx -> if
  | Just (i, _T) <- lookupInContext n ctx -> pure (QVar (Free i) ::: _T)
  | otherwise                             -> asks (\ ElabContext{ module', graph, sig } -> lookupInSig n module' graph (interfaces sig)) >>= \case
    Just (n ::: _T) -> do
      n ::: _T <- instantiate (QEOp n ::: _T)
      pure $ n ::: _T
    _ -> do
      n :=: _ ::: _T <- resolveQ n
      synth $ global (n ::: _T)

hole :: Name -> Check a
hole n = Check $ \ _T -> err $ Hole n _T

($$) :: Synth Quote -> Check Quote -> Synth Quote
f $$ a = Synth $ trace "$$" $ do
  f' ::: _F <- synth f
  (Binding _ _ s _A, _B) <- expectQuantifier "in application" _F
  a' <- extendSig s (check (a ::: _A))
  d <- depth
  pure $ QApp f' (Ex, a') ::: TSusp (_B (free d))


(|-) :: (HasCallStack, Has (State Context) sig m) => Name ::: Type -> m a -> m a
(n ::: _T) |- b = do
  i <- depth
  modify (|> Tm n _T)
  a <- b
  let extract (gamma :> Tm _ _) | i == level (Context gamma) = gamma
      extract (gamma :> e@Ty{})                              = extract gamma :> e
      extract (_     :> _)                                   = error "bad context entry"
      extract Nil                                            = error "bad context"
  a <$ modify (Context . extract . elems)

infix 1 |-


(>-) :: HasCallStack => Binding Value -> Elab a -> Elab a
-- FIXME: should this do something about the signature?
Binding _ n _s _T >- m = trace ">-" $ fromMaybe __ n ::: _T |- m

infix 1 >-


-- Expressions

synthExpr :: HasCallStack => S.Ann S.Expr -> Synth Quote
synthExpr (S.Ann s _ e) = mapSynth (trace "synthExpr" . setSpan s) $ case e of
  S.Var n      -> var n
  S.KType      -> _Type
  S.KInterface -> _Interface
  S.TString    -> _String
  S.TComp t    -> QTSusp <$> elabComp t
  S.App f a    -> synthExpr f $$ checkExpr a
  S.As t _T    -> as (checkExpr t ::: checkExpr _T)
  S.String s   -> string s
  S.Hole{}     -> nope
  S.Lam{}      -> nope
  S.Thunk{}    -> nope
  S.Force e    -> force (synthExpr e)
  where
  nope = Synth $ couldNotSynthesize (show e)

checkExpr :: HasCallStack => S.Ann S.Expr -> Check Quote
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


elabBinding :: S.Ann S.Binding -> [(Pos, Check (Binding Quote))]
elabBinding (S.Ann s _ (S.Binding p n d t)) =
  [ (start s, Check $ \ _T -> setSpan s . trace "elabBinding" $ do
    d' <- traverse (traverse (check . (::: KInterface) . elabSig)) d
    t' <- check (checkExpr t ::: _T)
    pure $ Binding p n d' t')
  | n <- maybe [Nothing] (map Just . toList) n ]

elabSig :: S.Ann S.Interface -> Check Quote
elabSig (S.Ann s _ (S.Interface (S.Ann s' _ n) sp)) = Check $ \ _T -> setSpan s . trace "elabSig" $
  check (switch (foldl' ($$) (mapSynth (setSpan s') (var n)) (checkExpr <$> sp)) ::: _T)

elabComp :: S.Ann S.Comp -> Synth QComp
elabComp (S.Ann s _ (S.Comp bs d t)) = Synth $ setSpan s . trace "elabComp" $
  foldr (\ b k bs -> do
    b' <- check (snd b ::: KType)
    env <- gets (fmap entryDef . elems)
    fmap (eval env) b' >- k (bs . (b':)))
  (\ bs' -> do
    d' <- traverse (traverse (check . (::: KInterface) . elabSig)) d
    t' <- check (checkExpr t ::: KType)
    -- FIXME: add the effect var and populate this authoritatively
    pure $ QComp (bs' []) (Sig Nothing (fromMaybe [] d')) t' ::: KType)
  (elabBinding =<< bs)
  id


_Type :: Synth Quote
_Type = Synth $ pure $ QKType ::: KType

_Interface :: Synth Quote
_Interface = Synth $ pure $ QKInterface ::: KType

_String :: Synth Quote
_String = Synth $ pure $ QTString ::: KType


lam :: Name -> Check Quote -> Check Quote
lam n b = Check $ \ _T -> trace "lam" $ do
  -- FIXME: error if the signature is non-empty; variable patterns don’t catch effects.
  (t@(Binding pl _ _s _A), _B) <- expectQuantifier "when checking lambda" _T
  -- FIXME: extend the signature if _B v is a TRet.
  d <- depth
  b' <- t >- check (b ::: TSusp (_B (free d)))
  pure $ QELam pl [(PVar n, b')]

thunk :: Check a -> Check a
thunk e = Check $ trace "thunk" . \case
  TSusp (TRet (Sig _ s) t) -> extendSig (Just s) $ check (e ::: t)
  t                        -> check (e ::: t)

force :: Synth a -> Synth a
force e = Synth $ trace "force" $ do
  e' ::: _T <- synth e
  -- FIXME: should we check the signature? or can we rely on it already having been checked?
  (_s, _T') <- expectRet "when forcing computation" _T
  pure $ e' ::: _T'


-- FIXME: go find the pattern matching matrix algorithm
elabClauses :: [S.Clause] -> Check Quote
elabClauses [S.Clause (S.Ann _ _ (S.PVal (S.Ann _ _ (S.PVar n)))) b] = lam n $ checkExpr b
elabClauses cs = Check $ \ _T -> do
  -- FIXME: use the signature to elaborate the pattern
  (Binding _ _ s _A, _B) <- expectQuantifier "when checking clauses" _T
  d <- depth
  -- FIXME: I don’t see how this can be correct; the context will not hold a variable but rather a pattern of them.
  let _B' = TSusp $ _B (free d)
  cs' <- for cs $ \ (S.Clause p b) -> elabPattern (fromMaybe [] s) _A p (\ p' -> do
    (tm <$> p',) <$> check (checkExpr b ::: _B'))
  pure $ QELam Ex cs'


-- FIXME: check for unique variable names
elabPattern :: [Value] -> Type -> S.Ann S.EffPattern -> (Pattern (Name ::: Type) -> Elab a) -> Elab a
elabPattern sig = go
  where
  go _A (S.Ann s _ p) k = trace "elabPattern" $ setSpan s $ case p of
    S.PVal p -> goVal _A p k
    S.PEff n ps v -> do
      ElabContext{ module' = mod, graph } <- ask
      case lookupInSig n mod graph sig of
        Just (q ::: _T') -> do
          _T'' <- inst _T'
          -- FIXME: this should get the ambient effect var
          subpatterns _T'' ps $ \ _T ps' -> k (PEff q (fromList ps') (v ::: TSusp (TForAll (Binding Ex Nothing Nothing _T) (const (TRet (Sig Nothing sig) _A)))))
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
    TForAll (Binding Im _ _s _T) _B -> meta _T >>= inst . _B . free
    _T                              -> pure (TSusp _T)
  subpatterns _T' = \case
    []   -> \ k -> k _T' []
    p:ps -> \ k -> do
      -- FIXME: assert that the signature is empty
      (t@(Binding _ _ _s _A), _B) <- expectQuantifier "when checking constructor pattern" _T'
      -- FIXME: is this right? should we use `free` instead? if so, what do we push onto the context?
      -- FIXME: I think this definitely isn’t right, as it instantiates variables which should remain polymorphic. We kind of need to open this existentially, I think?
      d <- depth
      t >- goVal _A p (\ p' -> subpatterns (TSusp (_B (free d))) ps (\ _T ps' -> k _T (p' : ps')))


string :: Text -> Synth Quote
string s = Synth $ pure $ QEString s ::: TString


-- Declarations

elabDataDef
  :: Has (Reader Graph :+: Reader MName :+: Reader Module :+: Throw Err :+: Time Instant :+: Trace) sig m
  => Name ::: Comp
  -> [S.Ann (Name ::: S.Ann S.Comp)]
  -> m [Name :=: Maybe Def ::: Comp]
-- FIXME: check that all constructors return the datatype.
elabDataDef (dname ::: _T) constructors = trace "elabDataDef" $ do
  mname <- ask
  cs <- for constructors $ runWithSpan $ \ (n ::: t) -> do
    let QComp bs _ _ = quoteComp 0 _T
    QComp bs' s t <- elab $ foldr (\ b k -> gets (fmap entryDef . elems) >>= \ env -> fmap (eval env) b >- k) (check (switch (elabComp t) ::: KType)) bs
    let c_T = evalComp Nil (QComp (bs <> bs') s t)
    pure $ n :=: Just (DTerm (con (mname :.: n) Nil c_T)) ::: c_T
  -- FIXME: constructor functions should have signatures, but constructors should not.
  pure
    $ (dname :=: Just (DData (scopeFromList cs)) ::: _T)
    : cs
  where
  con q fs = \case
    TForAll (Binding p n _s _T) _B -> ELam p [Clause (PVar (fromMaybe __ n)) (\ v -> let v' = unsafeUnPVar v in con q (fs :> v') (_B v'))]
    _T                             -> ECon (q :$ fs)

elabInterfaceDef
  :: Has (Reader Graph :+: Reader MName :+: Reader Module :+: Throw Err :+: Time Instant :+: Trace) sig m
  => Comp
  -> [S.Ann (Name ::: S.Ann S.Comp)]
  -> m (Maybe Def ::: Comp)
elabInterfaceDef _T constructors = trace "elabInterfaceDef" $ do
  cs <- for constructors $ runWithSpan $ \ (n ::: t) -> tracePretty n $ do
    -- FIXME: we should unpack the Comp instead of quoting so we don’t have to re-eval everything.
    let QComp bs _ _ = quoteComp 0 _T
    QComp bs' s t <- elab $ foldr (\ b k -> gets (fmap entryDef . elems) >>= \ env -> fmap (eval env) b >- k) (check (switch (elabComp t) ::: KType)) bs
    -- FIXME: check that the interface is a member of the sig.
    let _T = evalComp Nil (QComp (bs <> bs') s t)
    pure $ n :=: Nothing ::: _T
  pure $ Just (DInterface (scopeFromList cs)) ::: _T

-- FIXME: add a parameter for the effect signature.
elabTermDef
  :: (HasCallStack, Has (Reader Graph :+: Reader MName :+: Reader Module :+: Throw Err :+: Time Instant :+: Trace) sig m)
  => Comp
  -> S.Ann S.Expr
  -> m Expr
elabTermDef _T expr = runReader (S.ann expr) $ trace "elabTermDef" $ do
  elab $ eval Nil <$> check (go (checkExpr expr) ::: TSusp _T)
  where
  go k = Check $ \ _T -> case _T of
    TSusp (TForAll Binding{ name = Just n } _) -> check (lam n (go k) ::: _T)
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
    es <- trace "types" $ for ds $ \ (S.Ann _ _ (dname, S.Ann s _ (S.Decl tele def))) -> tracePretty dname $ local (const s) $ do
      -- FIXME: add the effect var to the QComp before evaluating.
      _T <- runModule . elab $ addEffectVar . evalComp Nil <$> check (switch (elabComp tele) ::: KType)

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
    trace "definitions" $ for_ (catMaybes es) $ \ (s, dname, t ::: _T) -> local (const s) $ tracePretty dname $ do
      t' <- runModule $ elabTermDef _T t
      scope_.decls_.ix dname .= (Just (DTerm t') ::: _T)


-- FIXME: do we need to shift levels internally? (how would levels be happening? this should be closed—but we certainly can’t /prove/ that it’s closed)
addEffectVar :: Comp -> Comp
addEffectVar _T = TForAll (Binding Im (Just "ε") Nothing KInterface) (\ _E -> insertEffectVar _E _T)

insertEffectVar :: Type -> Comp -> Comp
insertEffectVar _E = go
  where
  go = \case
    -- FIXME: we can probably skip implicits because otherwise we might try to insert effect vars into e.g. polykinds
    TForAll b@Binding{ type' } _B -> TForAll b{ type' = case type' of { TSusp c -> TSusp (go c) ; t -> t } } (go . _B)
    TRet s KType                  -> TRet s KType
    -- FIXME: is this right?
    TRet s t                      -> TRet s{ effectVar = Just _E } t


extendSig :: Has (Reader ElabContext) sig m => Maybe [Value] -> m a -> m a
extendSig = maybe id (locally (sig_.interfaces_) . (++))

depth :: Has (State Context) sig m => m Level
depth = gets @Context level

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

-- FIXME: add a constructor for more free-form errors?
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
  ctx <- get
  span <- view span_
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

expectQuantifier :: String -> Type -> Elab (Binding Value, Type -> Comp)
expectQuantifier = expectMatch (\case{ TForAll t b -> pure (t, b) ; _ -> Nothing } <=< stripEmpty) "{_} -> _"

stripEmpty :: Type -> Maybe Comp
stripEmpty = \case
  TSusp (TRet (Sig Nothing []) t) -> stripEmpty t
  TSusp t                         -> Just t
  _                               -> Nothing

expectRet :: String -> Type -> Elab (Sig Value, Type)
expectRet = expectMatch (\case { TSusp (TRet s t) -> pure (s, t) ; _ -> Nothing }) "{_}"


-- Machinery

data ElabContext = ElabContext
  { graph   :: Graph
  , _mname  :: MName
  , module' :: Module
  , sig     :: Sig Value
  , span    :: Span
  }

sig_ :: Lens' ElabContext (Sig Value)
sig_ = lens sig (\ e sig -> e{ sig })

span_ :: Lens' ElabContext Span
span_ = lens (span :: ElabContext -> Span) (\ e span -> (e :: ElabContext){ span })


onTop :: HasCallStack => (Level -> Name :=: Maybe Value ::: Type -> Elab (a, Maybe Suffix)) -> Elab a
onTop f = do
  ctx <- get
  (gamma, elem) <- case elems ctx of
    gamma :> elem -> pure (Context gamma, elem)
    Nil           -> error "wtf empty context" -- FIXME: make this a real error
  put gamma
  case elem of
    Ty n v _T -> f (level gamma) (n :=: v ::: _T) >>= \ (a, x) -> a <$ case x of
      Just v  -> modify (<>< v)
      Nothing -> modify (|> elem)
    _         -> onTop f <* modify (|> elem)


solve :: HasCallStack => Level -> Type -> Elab Type
solve v = go v []
  where
  go v ext t = onTop $ \ g (n :=: d ::: _K) -> case (g == v, occursIn (== Free g) t || occursInSuffix (== Free g) ext, d) of
    (True,  True,  _)       -> mismatch "infinite type" (Right (free g)) t
    (True,  False, Nothing) -> replace (ext ++ [ n :=: Just t ::: _K ]) t
    (True,  False, Just t') -> modify (<>< ext) >> unify t' t >>= restore
    (False, True,  _)       -> go v ((n :=: d ::: _K):ext) t >>= replace []
    (False, False, _)       -> go v ext t >>= restore

  occursInSuffix m = any (\ (_ :=: v ::: _T) -> maybe False (occursIn m) v || occursIn m _T)

-- FIXME: we don’t get good source references during unification
unify :: HasCallStack => Type -> Type -> Elab Type
unify t1 t2 = case (t1, t2) of
  (VNe (Free v1 :$ Nil), VNe (Free v2 :$ Nil)) -> onTop $ \ g (n :=: d ::: _K) -> case (g == v1, g == v2, d) of
    (True,  True,  _)       -> restore (free v1)
    (True,  False, Nothing) -> replace [n :=: Just (free v2) ::: _K] (free v2)
    (False, True,  Nothing) -> replace [n :=: Just (free v1) ::: _K] (free v1)
    (True,  False, Just t)  -> unify (free v2) t >>= restore
    (False, True,  Just t)  -> unify (free v1) t >>= restore
    (False, False, _)       -> unify (free v1) (free v2) >>= restore
  (VNe (Free v1 :$ Nil), t2)                   -> solve v1 t2
  (t1, VNe (Free v2 :$ Nil))                   -> solve v2 t1
  (KType, KType)                               -> pure KType
  (KType, _)                                   -> nope
  (KInterface, KInterface)                     -> pure KInterface
  (KInterface, _)                              -> nope
  (TSusp c1, TSusp c2)                         -> TSusp <$> comp c1 c2
  (TSusp (TRet (Sig Nothing []) t1), t2)       -> unify t1 t2
  (t1, TSusp (TRet (Sig Nothing []) t2))       -> unify t1 t2
  (TSusp{}, _)                                 -> nope
  (ELam{}, ELam{})                             -> nope
  (ELam{}, _)                                  -> nope
  (VNe (v1 :$ sp1), VNe (v2 :$ sp2))           -> foldl' (C.$$) <$> var v1 v2 <*> spine (pl unify) sp1 sp2
  (VNe{}, _)                                   -> nope
  (ECon (q1 :$ sp1), ECon (q2 :$ sp2))         -> ECon . (q1 :$) <$ unless (q1 == q2) nope <*> spine unify sp1 sp2
  (ECon{}, _)                                  -> nope
  (TString, TString)                           -> pure TString
  (TString, _)                                 -> nope
  (EString e1, EString e2)                     -> EString e1 <$ unless (e1 == e2) nope
  (EString{}, _)                               -> nope
  (EOp (q1 :$ sp1), EOp (q2 :$ sp2))           -> EOp . (q1 :$) <$ unless (q1 == q2) nope <*> spine (pl unify) sp1 sp2
  (EOp{}, _)                                   -> nope
  where
  nope = couldNotUnify "mismatch" t1 t2

  var v1 v2 = case (v1, v2) of
    (Global q1, Global q2) -> C.global q1 <$ unless (q1 == q2) nope
    (Global{}, _)          -> nope
    (Free v1, Free v2)     -> C.free v1 <$ unless (v1 == v2) nope
    (Free{}, _)            -> nope

  pl f (p1, t1) (p2, t2) = (p1,) <$ unless (p1 == p2) nope <*> f t1 t2

  spine f sp1 sp2 = unless (length sp1 == length sp2) nope *> sequenceA (zipWith f sp1 sp2)

  comp c1 c2 = case (c1, c2) of
    (TForAll t1 b1, TForAll t2 b2) -> TForAll <$> binding t1 t2 <*> do { d <- depth ; b' <- comp (b1 (free d)) (b2 (free d)) ; pure (\ v -> bindComp d v b') }
    (TForAll{}, _)                 -> nope
    (TRet s1 t1, TRet s2 t2)       -> TRet <$> sig s1 s2 <*> unify t1 t2
    (TRet{}, _)                    -> nope

  binding (Binding p1 n1 d1 t1) (Binding p2 _ d2 t2) = Binding p1 n1 <$ unless (p1 == p2) nope <*> eff (spine unify) d1 d2 <*> unify t1 t2

  sig (Sig e1 c1) (Sig e2 c2) = Sig <$> eff unify e1 e2 <*> spine unify c1 c2

  eff f e1 e2 = case (e1, e2) of
    (Nothing, Nothing) -> pure Nothing
    (Just e1, Just e2) -> Just <$> f e1 e2
    _                  -> nope


newtype Elab a = Elab { runElab :: forall sig m . Has (Reader ElabContext :+: State Context :+: Throw Err :+: Trace) sig m => m a }

instance Functor Elab where
  fmap f (Elab m) = Elab (fmap f m)

instance Applicative Elab where
  pure a = Elab $ pure a
  Elab f <*> Elab a = Elab (f <*> a)

instance Monad Elab where
  Elab m >>= f = Elab $ m >>= runElab . f

instance Algebra (Reader ElabContext :+: State Context :+: Throw Err :+: Trace) Elab where
  alg hdl sig ctx = case sig of
    L rctx          -> Elab $ alg (runElab . hdl) (inj rctx)  ctx
    R (L sctx)      -> Elab $ alg (runElab . hdl) (inj sctx)  ctx
    R (R (L throw)) -> Elab $ alg (runElab . hdl) (inj throw) ctx
    R (R (R trace)) -> Elab $ alg (runElab . hdl) (inj trace) ctx

elab :: Has (Reader Graph :+: Reader MName :+: Reader Module :+: Reader Span :+: Throw Err :+: Time Instant :+: Trace) sig m => Elab a -> m a
elab = evalState Context.empty . (\ m -> do { ctx <- mkContext ; runReader ctx m}) . runElab
  where
  mkContext = ElabContext <$> ask <*> ask <*> ask <*> pure (Sig Nothing []) <*> ask


check :: (Check a ::: Type) -> Elab a
check (m ::: _T) = trace "check" $ case _T of
  -- TSusp (TRet sig _) -> extendSig sig (runCheck m _T)
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
