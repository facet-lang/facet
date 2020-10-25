-- | This module defines the /elaboration/ of terms in 'S.Expr' into values in 'Value'.
--
-- Elaboration is the only way 'Value's are constructed from untrusted terms, and so typechecking is performed at this point. If elaboration succeeds and a 'Value' is returned, that 'Value' does not require further verification; hence, 'Value's elide source span information.
module Facet.Elab
( Type
, Expr
, Elab(..)
, elab
, elabWith
, Check(..)
, Synth(..)
, check
, unify
  -- * General
, global
  -- * Expressions
, elabExpr
, _Type
, (>~>)
, ($$)
, lam
  -- * Modules
, elabModule
, apply
  -- * Errors
, Err(..)
, Reason(..)
) where

import           Control.Algebra
import           Control.Applicative (liftA2)
import           Control.Carrier.Error.Church
import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Effect.Empty
import           Control.Effect.Lens ((%=), (.=))
import           Control.Effect.Sum
import           Control.Lens (ifor_, ix)
import           Data.Bifunctor (first)
import           Data.Foldable (foldl', toList)
import qualified Data.IntMap as IntMap
import           Data.List.NonEmpty (NonEmpty(..), nonEmpty)
import qualified Data.Set as Set
import           Data.Traversable (for, mapAccumL)
import           Facet.Context as Context
import           Facet.Core hiding (global, ($$))
import qualified Facet.Core as C
import           Facet.Effect.Trace as Trace
import           Facet.Graph as Graph
import           Facet.Name hiding (L, R)
import           Facet.Span (Span(..))
import           Facet.Stack hiding ((!?))
import qualified Facet.Surface as S
import           Facet.Syntax
import           GHC.Stack

type Type = Value
type Expr = Value
type Prob = Value

type Subst = IntMap.IntMap (Maybe Prob ::: Type)

newtype Elab a = Elab { runElab :: forall sig m . Has (Reader (Context Type) :+: Reader Graph :+: Reader Module :+: Reader Span :+: State Subst :+: Throw Err :+: Trace) sig m => m a }

instance Functor Elab where
  fmap f (Elab m) = Elab (fmap f m)

instance Applicative Elab where
  pure a = Elab $ pure a
  Elab f <*> Elab a = Elab (f <*> a)

instance Monad Elab where
  Elab m >>= f = Elab $ m >>= runElab . f

instance Algebra (Reader (Context Type) :+: Reader Graph :+: Reader Module :+: Reader Span :+: State Subst :+: Throw Err :+: Trace) Elab where
  alg hdl sig ctx = case sig of
    L rctx                      -> Elab $ alg (runElab . hdl) (inj rctx) ctx
    R (L rspan)                 -> Elab $ alg (runElab . hdl) (inj rspan) ctx
    R (R (L graph))             -> Elab $ alg (runElab . hdl) (inj graph) ctx
    R (R (R (L mod)))           -> Elab $ alg (runElab . hdl) (inj mod) ctx
    R (R (R (R (L subst))))     -> Elab $ alg (runElab . hdl) (inj subst) ctx
    R (R (R (R (R (L throw))))) -> Elab $ alg (runElab . hdl) (inj throw) ctx
    R (R (R (R (R (R trace))))) -> Elab $ alg (runElab . hdl) (inj trace) ctx

elab :: Has (Reader Graph :+: Reader Module :+: Reader Span :+: Throw Err :+: Trace) sig m => Elab Value -> m Value
elab = elabWith apply

elabWith :: Has (Reader Graph :+: Reader Module :+: Reader Span :+: Throw Err :+: Trace) sig m => (Subst -> a -> m b) -> Elab a -> m b
elabWith f = runSubstWith f . runContext . runElab


newtype Check a = Check { runCheck :: Type -> Elab a }
  deriving (Algebra (Reader Type :+: Reader (Context Type) :+: Reader Graph :+: Reader Module :+: Reader Span :+: State Subst :+: Throw Err :+: Trace), Applicative, Functor, Monad) via ReaderC Type Elab

newtype Synth a = Synth { synth :: Elab (a ::: Type) }

instance Functor Synth where
  fmap f (Synth m) = Synth (first f <$> m)

check :: (Check a ::: Type) -> Elab a
check (m ::: _T) = runCheck m _T


checkElab :: (Maybe Type -> Elab (a ::: Type)) -> Check a
checkElab f = tm <$> Check (f . Just)

synthElab :: (Maybe Type -> Elab (a ::: Type)) -> Synth a
synthElab f = Synth (f Nothing)


unify :: Type :===: Type -> Elab Type
unify = \case
  -- FIXME: this is missing a lot of cases
  VType                 :===: VType                 -> pure VType
  VInterface            :===: VInterface            -> pure VInterface
  -- FIXME: resolve globals to try to progress past certain inequalities
  VNeut h1 e1           :===: VNeut h2 e2
    | h1 == h2
    , Just e' <- unifyS (e1 :===: e2)               -> VNeut h1 <$> e'
  VNeut (Metavar v) Nil :===: x                     -> solve (tm v :=: x)
  x                     :===: VNeut (Metavar v) Nil -> solve (tm v :=: x)
  VForAll t1 b1         :===: VForAll t2 b2
    | _pl t1 == _pl t2, delta t1 == delta t2 -> do
      -- FIXME: unify the signatures
      t <- unify ((type' :: Binding -> Type) t1 :===: (type' :: Binding -> Type) t2)
      d <- asks @(Context Type) level
      let v = free d
      b <- unify (b1 v :===: b2 v)
      pure $ VForAll (Binding (_pl t1) ((name :: Binding -> UName) t1) (delta t1) t) (\ v -> C.bind d v b)
  -- FIXME: build and display a diff of the root types
  t1                    :===: t2                    -> couldNotUnify "mismatch" t1 t2
  where
  unifyS (Nil           :===: Nil)           = Just (pure Nil)
  -- NB: we make no attempt to unify case eliminations because they shouldn’t appear in types anyway.
  unifyS (i1 :> EApp l1 :===: i2 :> EApp l2)
    | pl l1 == pl l2                         = liftA2 (:>) <$> unifyS (i1 :===: i2) <*> Just (EApp . P (pl l1) <$> unify (out l1 :===: out l2))
  unifyS _                                   = Nothing

  solve (n :=: val') = do
    subst <- get
    -- FIXME: occurs check
    case subst IntMap.! getMeta n of
      Just val ::: _T -> unify (val' :===: val)
      Nothing  ::: _T -> val' <$ put (insertSubst n (Just val' ::: _T) subst)


-- FIXME: should we give metas names so we can report holes or pattern variables cleanly?
meta :: Type -> Elab (Meta ::: Type)
meta _T = do
  subst <- get
  let m = Meta (length subst)
  (m ::: _T) <$ put (insertSubst m (Nothing ::: _T) subst)

insertSubst :: Meta -> Maybe Prob ::: Type -> Subst -> Subst
insertSubst n (v ::: _T) = IntMap.insert (getMeta n) (v ::: _T)

-- FIXME: does instantiation need to be guided by the expected type?
-- FIXME: can implicits have effects? what do we do about the signature?
instantiate :: Expr ::: Type -> Elab (Expr ::: Type)
instantiate (e ::: _T) = case unForAll _T of
  Just (Binding Im _ _ _T, _B) -> do
    m <- metavar <$> meta _T
    instantiate (e C.$$ im m ::: _B m)
  _                        -> pure $ e ::: _T


-- General

switch
  :: Synth Value
  -> Maybe Type
  -> Elab (Value ::: Type)
switch (Synth m) = \case
  Just _K -> m >>= \ (a ::: _K') -> (a :::) <$> unify (_K' :===: _K)
  _       -> m

resolveWith
  :: (forall sig m . Has Empty sig m => Module -> m (QName :=: Maybe Def ::: Value))
  -> Maybe MName
  -> DName
  -> Synth QName
resolveWith lookup m n = Synth $ asks lookup >>= \case
  Just (n' :=: _ ::: _T) -> pure $ n' ::: _T
  Nothing                -> do
    g <- ask @Graph
    let defs = foldMap (lookup . snd) (getGraph g)
    case defs of
      []                -> freeVariable m n
      [n' :=: _ ::: _T] -> pure $ n' ::: _T
      -- FIXME: resolve ambiguities by type.
      _                 -> ambiguousName m n (map (\ (q :=: _ ::: _) -> q) defs)

resolve
  :: DName
  -> Synth QName
resolve n = resolveWith (lookupD n) Nothing n

resolveC
  :: UName
  -> Synth QName
resolveC n = resolveWith (lookupC n) Nothing (C n)

resolveQ
  :: QName
  -> Synth QName
resolveQ q@(m :.: n) = Synth $ lookupQ q <$> ask <*> ask >>= \case
  Just (q' :=: _ ::: _T) -> pure $ q' ::: _T
  Nothing                -> freeVariable (Just m) n

-- FIXME: we’re instantiating when inspecting types in the REPL.
global
  :: Synth QName
  -> Synth Value
global n = Synth $ do
  q <- synth n
  instantiate (C.global q ::: ty q)

-- FIXME: do we need to instantiate here to deal with rank-n applications?
var
  :: Maybe MName
  -> DName
  -> Synth Value
var m n = case m of
  Nothing
    | Just u <- eOrT n -> Synth $ ask >>= \ ctx -> case lookupLevel u ctx of
      Nothing      -> synth $ global (resolve n)
      Just (i, _T) -> pure (free i ::: _T)
    | otherwise        -> global (resolve n)
  Just m -> global (resolveQ (m :.: n))
  where
  eOrT (E n) = Just n
  eOrT (T n) = Just n
  eOrT _     = Nothing

hole
  :: UName
  -> Check a
hole n = Check $ \ _T -> err $ Hole n _T

($$)
  :: Synth Value
  -> Check Value
  -> Synth Value
f $$ a = Synth $ do
  f' ::: _F <- synth f
  (_A, _B) <- expectQuantifier "in application" _F
  a' <- check (a ::: (type' :: Binding -> Type) _A)
  pure $ (f' C.$$ ex a') ::: _B a'


elabBinder
  :: Has (Reader (Context Type)) sig m
  => (Value -> m Value)
  -> m (Value -> Value)
elabBinder b = do
  d <- asks @(Context Type) level
  b' <- b (free d)
  pure $ \ v -> C.bind d v b'

(|-)
  :: Has (Reader (Context Type)) sig m
  => UName ::: Type
  -> m a
  -> m a
t |- b = local @(Context Type) (|> t) b

infix 1 |-

(|-*)
  :: (Has (Reader (Context Type)) sig m, Traversable t)
  => t (UName ::: Type)
  -> m Value
  -> m (t Value -> Value)
p |-* b = do
  ctx <- ask @(Context Type)
  let d = level ctx
      (_, ext) = foldl' (\ (d, ctx) t -> (succ d, ctx . (|> t))) (d, id) p
  b' <- local ext b
  pure $ \ p -> snd (foldl' (\ (d, b') v -> (succ d, C.bind d v b')) (succ d, b') p)

infix 1 |-*


-- Expressions

elabExpr
  :: HasCallStack
  => S.Ann S.Expr
  -> Maybe Type
  -> Elab (Expr ::: Type)
elabExpr = withSpan' $ \case
  S.Var m n       -> switch $ var m n
  S.Hole  n       -> check (hole n) "hole"
  S.Type          -> switch _Type
  S.Interface     -> switch _Interface
  S.ForAll bs s b -> elabTelescope bs s b
  S.App f a       -> switch $ synthElab (elabExpr f) $$ checkElab (elabExpr a)
  S.Comp cs       -> check (elabComp cs) "computation"
  where
  check m msg _T = expectChecked _T msg >>= \ _T -> (::: _T) <$> runCheck m _T

-- FIXME: elaborate the signature.
elabTelescope :: [S.Ann S.Binding] -> [S.Ann S.Delta] -> S.Ann S.Type -> Maybe Type -> Elab (Type ::: Type)
elabTelescope bindings _ body = foldr (\ (S.Ann s (S.Binding p ns _ t)) b ->
  setSpan (Span (start s) (end (S.ann body))) . foldr (\ n k ->
    switch $ P p n ::: checkElab (elabExpr t) >~> \ v -> v |- checkElab k) b ns) (elabExpr body) bindings


_Type :: Synth Type
_Type = Synth $ pure $ VType ::: VType

_Interface :: Synth Type
_Interface = Synth $ pure $ VInterface ::: VType

-- FIXME: effects!
(>~>)
  :: (Pl_ UName ::: Check Type)
  -> (UName ::: Type -> Check Type)
  -> Synth Type
(n ::: t) >~> b = Synth $ do
  _T <- check (t ::: VType)
  b' <- elabBinder $ \ _ -> check (b (out n ::: _T) ::: VType)
  pure $ VForAll (Binding (pl n) (out n) mempty _T) b' ::: VType

infixr 1 >~>


lam
  :: Pl_ UName
  -> (UName ::: Type -> Check Expr)
  -> Check Expr
lam n b = Check $ \ _T -> do
  -- FIXME: how does the effect adjustment change this?
  (Binding _ _ _ _T, _B) <- expectQuantifier "when checking lambda" _T
  b' <- elabBinder $ \ v -> check (b (out n ::: _T) ::: _B v)
  pure $ VLam (Binding (pl n) (out n) mempty _T) b'


elabComp
  :: HasCallStack
  => S.Ann S.Comp
  -> Check Expr
elabComp = withSpan $ \case
  S.Expr    b  -> checkElab (elabExpr b)
  S.Clauses cs -> elabClauses cs

data XOr a b
  = XB
  | XL a
  | XR b
  | XT

instance (Semigroup a, Semigroup b) => Semigroup (XOr a b) where
  XB   <> b    = b
  a    <> XB   = a
  XL a <> XL b = XL (a <> b)
  XR a <> XR b = XR (a <> b)
  _    <> _    = XT

instance (Semigroup a, Semigroup b) => Monoid (XOr a b) where
  mempty = XB

elabClauses :: [(NonEmpty (S.Ann S.Pattern), S.Ann S.Expr)] -> Check Expr
elabClauses [((S.Ann _ (S.PVar n)):|ps, b)] = Check $ \ _T -> do
  -- FIXME: error if the signature is non-empty; variable patterns don’t catch effects.
  (Binding pl _ s _A, _B) <- expectQuantifier "when checking clauses" _T
  b' <- elabBinder $ \ v -> n ::: _A |- check (maybe (checkElab (elabExpr b)) (elabClauses . pure . (,b)) (nonEmpty ps) ::: _B v)
  pure $ VLam (Binding pl n s _A) b'
-- FIXME: this is incorrect in the presence of wildcards (or something). e.g. { (true) (true) -> true, _ _ -> false } gets the inner {(true) -> true} clause from the first case appended to the
elabClauses cs = Check $ \ _T -> do
  rest <- case foldMap partitionClause cs of
    XB    -> pure Nothing
    XL _  -> pure Nothing
    XR cs -> pure $ Just cs
    XT    -> error "mixed" -- FIXME: throw a proper error
  -- FIXME: use the signature to elaborate the pattern
  (Binding _ _ s _A, _B) <- expectQuantifier "when checking clauses" _T
  b' <- elabBinder $ \ v -> do
    let _B' = _B v
    cs' <- for cs $ \ (p:|_, b) -> do
      p' <- check (elabPattern p ::: _A)
      b' <- p' |-* check (maybe (checkElab (elabExpr b)) elabClauses rest ::: _B')
      pure (p', b')
    pure $ case' v cs'
  -- FIXME: something isn’t correctly accounting for the insertion of the lambda.
  -- e.g. the elaboration of fst & snd contain case c { (pair d e) -> c } and case c { (pair d e) -> d } respectively. is the context being extended incorrectly, or not being extended when it should be?
  pure $ VLam (Binding Ex __ s _A) b'
  where
  partitionClause (_:|ps, b) = case ps of
    []   -> XL ()
    p:ps -> XR [(p:|ps, b)]


elabPattern
  :: S.Ann S.Pattern
  -> Check (C.Pattern Type (UName ::: Type))
elabPattern = withSpan $ \case
  S.PVar n      -> Check $ \ _T -> pure (C.PVar (n ::: _T))
  S.PCon n ps   -> Check $ \ _T -> do
    let inst _T = case unForAll _T of
          Just (Binding Im _ _ _T, _B) -> do
            m <- metavar <$> meta _T
            inst (_B m)
          _                        -> pure _T
        go _T' = \case
          []   -> [] <$ unify (_T' :===: _T)
          p:ps -> do
            -- FIXME: check the signature? somehow?
            (Binding _ _ _ _A, _B) <- expectQuantifier "when checking constructor pattern" _T'
            -- FIXME: there’s no way this is going to work, let alone a good idea
            -- FIXME: elaborate patterns in CPS, binding locally with elabBinder, & obviating the need for |-*.
            v <- metavar <$> meta _A
            p' <- check (elabPattern p ::: _A)
            ps' <- go (_B v) ps
            pure $ p' : ps'
    q ::: _T' <- synth (resolveC n)
    _T'' <- inst _T'
    C.PCon . Con (q ::: _T'') . fromList <$> go _T'' (toList ps)
  S.PEff{}      -> error "TBD"


-- Declarations

elabDataDef
  :: HasCallStack
  => [S.Ann S.Binding]
  -> [S.Ann (UName ::: S.Ann S.Type)]
  -> Check [UName ::: Type]
elabDataDef bindings constructors = for constructors $ withSpan $ \ (n ::: t) -> (n :::) <$> wrap (checkElab (elabExpr t))
  where
  -- FIXME: check that all constructors return the datatype.
  wrap = flip (foldr (\ (S.Ann s (S.Binding _ ns _ _)) k ->
    setSpan s $ foldr (\ n k -> Check $ \ _T -> do
      (Binding _ _ s _T, _B) <- expectQuantifier "in type quantifier" _T
      b' <- elabBinder $ \ v -> check ((n ::: _T |- k) ::: _B v)
      pure $ VForAll (Binding Im n s _T) b') k ns)) bindings

elabInterfaceDef
  :: HasCallStack
  => [S.Ann S.Binding]
  -> [S.Ann (UName ::: S.Ann S.Type)]
  -> Check [UName ::: Type]
elabInterfaceDef bindings constructors = for constructors $ withSpan $ \ (n ::: t) -> (n :::) <$> setSpan (S.ann t) (wrap (end (S.ann t)) (checkElab (elabExpr t)))
  where
  wrap end = flip (foldr (\ (S.Ann s (S.Binding _ ns _ _)) k ->
    setSpan (Span (start s) end) $ foldr (\ n k -> Check $ \ _T -> do
      (Binding _ _ s _T, _B) <- expectQuantifier "in type quantifier" _T
      b' <- elabBinder $ \ v -> check ((n ::: _T |- k) ::: _B v)
      pure $ VForAll (Binding Im n s _T) b') k ns)) bindings

elabTermDef
  :: HasCallStack
  => [S.Ann S.Binding]
  -> S.Ann S.Expr
  -> Check Expr
elabTermDef bindings expr = foldr (\ (S.Ann s (S.Binding p ns _ _)) b ->
  setSpan s $ foldr (\ n k ->
    lam (P p n) (|- k)) b ns)
    (checkElab (elabExpr expr))
    bindings


-- Modules

elabModule
  :: forall m sig
  .  (HasCallStack, Has (Reader Graph) sig m, Has (Throw Err) sig m, Has Trace sig m)
  => S.Ann S.Module
  -> m C.Module
elabModule (S.Ann s (S.Module mname is os ds)) = execState (Module mname [] os []) . runReader s $ tracePretty mname $ do
  let (importedNames, imports) = mapAccumL (\ names (S.Ann _ S.Import{ name }) -> (Set.insert name names, Import name)) Set.empty is
  imports_ .= imports

  local (`restrict` importedNames) $ do
    -- FIXME: trace the defs as we elaborate them
    -- FIXME: maybe figure out the graph for mutual recursion?

    -- elaborate all the types first
    -- FIXME: do we need to pass the delta to elabTermDef and elabDataDef?
    es <- for ds $ \ (S.Ann _ (dname, S.Ann s (S.Decl bs delta (ty :=: def)))) -> tracePretty dname $ setSpan s $ do
      _T <- runModule . elab $ check (checkElab (elabTelescope bs delta ty) ::: VType)

      decls_ %= (<> [Decl dname Nothing _T])

      pure (s, dname, (bs, def) ::: _T)

    -- then elaborate the terms
    ifor_ es $ \ index (s, dname, (bs, def) ::: _T) -> setSpan s $ do
      def <- case def of
        S.DataDef cs -> do
          (s, cs) <- runModule . elabWith (fmap pure . (,)) $ check (elabDataDef bs cs ::: _T)
          C.DData <$> for cs (\ (n ::: _T) -> do
            _T' <- apply s _T
            let go fs = \case
                  VForAll _T _B -> VLam _T (\ v -> go (fs :> v) (_B v))
                  _T            -> VCon (Con (mname :.: C n ::: _T) fs)
            c <- apply s (go Nil _T')
            pure $ n :=: c ::: _T')

        S.InterfaceDef os -> do
          (s, os) <- runModule . elabWith (fmap pure . (,)) $ check (elabInterfaceDef bs os ::: _T)
          C.DInterface <$> for os (\ (n ::: _T) -> do
            _T' <- apply s _T
            let go fs = \case
                  VForAll _T _B -> VLam _T (\ v -> go (fs :> v) (_B v))
                  _T            -> VCon (Con (mname :.: C n ::: _T) fs)
            c <- apply s (go Nil _T')
            pure $ n :=: c ::: _T')

        S.TermDef t -> C.DTerm <$> runModule (elab (check (elabTermDef bs t ::: _T)))
      decls_.ix index .= Decl dname (Just def) _T


-- | Apply the substitution to the value.
apply :: Applicative m => Subst -> Expr -> m Value
apply s v = pure $ subst (IntMap.mapMaybe tm s) v -- FIXME: error if the substitution has holes.

emptySubst :: Subst
emptySubst = IntMap.empty

runSubstWith :: (Subst -> a -> m b) -> StateC Subst m a -> m b
runSubstWith with = runState with emptySubst

runContext :: ReaderC (Context Type) m a -> m a
runContext = runReader Context.empty

runModule :: Has (State Module) sig m => ReaderC Module m a -> m a
runModule m = do
  mod <- get
  runReader mod m


-- Errors

setSpan :: Has (Reader Span) sig m => Span -> m a -> m a
setSpan = local . const

withSpan :: Has (Reader Span) sig m => (a -> m b) -> S.Ann a -> m b
withSpan k (S.Ann s a) = setSpan s (k a)

withSpan' :: Has (Reader Span) sig m => (a -> b -> m c) -> S.Ann a -> b -> m c
withSpan' k (S.Ann s a) b = setSpan s (k a b)


data Err = Err
  { span      :: Span
  , reason    :: Reason
  , context   :: Context Type
  , callStack :: Stack Message
  }

data Reason
  = FreeVariable (Maybe MName) DName
  -- FIXME: add source references for the imports, definition sites, and any re-exports.
  | AmbiguousName (Maybe MName) DName [QName]
  | CouldNotSynthesize String
  | Mismatch String (Either String Type) Type
  | Hole UName Type


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

freeVariable :: Maybe MName -> DName -> Elab a
freeVariable m n = err $ FreeVariable m n

ambiguousName :: Maybe MName -> DName -> [QName] -> Elab a
ambiguousName n d qs = err $ AmbiguousName n d qs

expectChecked :: Maybe Type -> String -> Elab Type
expectChecked t msg = maybe (couldNotSynthesize msg) pure t


-- Patterns

expectMatch :: (Type -> Maybe out) -> String -> String -> Type -> Elab out
expectMatch pat exp s _T = maybe (mismatch s (Left exp) _T) pure (pat _T)

expectQuantifier :: String -> Type -> Elab (Binding, Type -> Type)
expectQuantifier = expectMatch unForAll "{_} -> _"
