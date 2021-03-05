{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Facet.Elab.Term
( -- * Term combinators
  global
, var
, tlam
, lam
, string
  -- * Polarity shifts
, force
, thunk
, (>>-)
  -- * General combinators
, instantiate
, hole
, switch
, as
  -- * Pattern combinators
, wildcardP
, varP
, conP
, fieldsP
, allP
, effP
  -- * Expression elaboration
, synthExprNeg
, synthExprPos
, checkExprNeg
, checkExprPos
, bindPattern
  -- * Declarations
, elabDataDef
, elabInterfaceDef
, elabTermDef
  -- * Modules
, elabModule
  -- * Judgements
, check
, Check(..)
, mapCheck
, Synth(..)
, mapSynth
, bind
, Bind(..)
, mapBind
) where

import           Control.Algebra
import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Effect.Lens (view, views, (.=))
import           Control.Effect.Throw
import           Control.Effect.Writer
import           Control.Lens (at, ix)
import           Control.Monad ((<=<))
import           Data.Bifunctor (first)
import           Data.Foldable
import           Data.Functor
import           Data.Maybe (catMaybes, fromMaybe)
import qualified Data.Set as Set
import           Data.Text (Text)
import           Data.Traversable (for, mapAccumL)
import           Facet.Context (Binding(..), toEnv)
import           Facet.Core.Module as Module
import           Facet.Core.Term as E
import           Facet.Core.Type as T hiding (global)
import           Facet.Effect.Write
import           Facet.Elab
import           Facet.Elab.Type
import           Facet.Graph
import           Facet.Lens
import           Facet.Name
import           Facet.Semiring (Few(..), zero, (><<))
import           Facet.Snoc
import           Facet.Source (Source)
import qualified Facet.Surface as S
import           Facet.Syntax
import           Facet.Usage hiding (restrict)
import           GHC.Stack

-- Term combinators

-- FIXME: how the hell are we supposed to handle instantiation?
global :: QName ::: Type -> Synth PType m (Pos Expr)
global (q ::: _T) = Synth $ pure $ varE (Global q) ::: _T

-- FIXME: do we need to instantiate here to deal with rank-n applications?
-- FIXME: effect ops not in the sig are reported as not in scope
-- FIXME: effect ops in the sig are available whether or not they’re in scope
var :: (HasCallStack, Has (Throw Err) sig m) => QName -> Synth PType m (Pos Expr)
var n = Synth $ ask >>= \ StaticContext{ module', graph } -> ask >>= \ ElabContext{ context, sig } -> if
  | Just (i, q, STerm _T) <- lookupInContext n context                      -> use i q $> (varE (Free i) ::: _T)
  | Just (_ :=: DTerm (Just x) _T) <- lookupInSig n module' graph sig -> pure (x ::: getPos _T)
  | otherwise                                                         -> do
    n :=: d <- resolveQ n
    _T <- case d of
      DTerm _ _T -> pure _T
      _          -> freeVariable n
    synth $ global (n ::: getPos _T)


-- | Elaborate a thunked type lambda from its body.
tlam :: (HasCallStack, Has (Throw Err) sig m) => Check NType m (Neg Expr) -> Check PType m (Pos Expr)
tlam b = Check $ \ _T -> do
  (n ::: _A, _B) <- expectQuantifier "when checking type abstraction" =<< expectThunk "when elaborating type abstraction" _T
  d <- depth
  b' <- Binding n zero (SType _A) |- check (b ::: _B (free d))
  pure $ thunkE (tlamE b')

-- | Elaborate a thunked lambda from its clauses.
lam :: (HasCallStack, Has (Throw Err) sig m) => [(Bind m (Pattern Name), Check NType m (Neg Expr))] -> Check PType m (Pos Expr)
lam cs = Check $ \ _T -> do
  (_A, _B) <- expectTacitFunction "when checking function" =<< expectThunk "when checking function" _T
  thunkE . lamE <$> traverse (\ (p, b) -> check (bind (p ::: _A) b ::: _B)) cs


app :: (HasCallStack, Has (Throw Err) sig m) => Synth NType m (Neg Expr) -> Check PType m (Pos Expr) -> Synth NType m (Neg Expr)
app f a = Synth $ do
  f' ::: _F <- synth f
  (_ ::: (q, _A), _B) <- expectFunction "in application" _F
  -- FIXME: test _A for Comp and extend the sig
  a' <- censor @Usage (q ><<) $ check (a ::: _A)
  pure $ appE f' a' ::: _B


string :: Text -> Synth PType m (Pos Expr)
string s = Synth $ pure $ stringE s ::: T.String


-- Polarity shifts

force :: Has (Throw Err) sig m => Check PType m (Pos Expr) -> Check NType m (Neg Expr)
force t = Check $ \ _T -> forceE <$> check (t ::: Thunk _T)

thunk :: (HasCallStack, Has (Throw Err) sig m) => Check NType m (Neg Expr) -> Check PType m (Pos Expr)
thunk c = Check $ fmap thunkE . check . (c :::) <=< expectThunk "when thunking computation"

(>>-) :: Has (Throw Err) sig m => Synth NType m (Neg Expr) -> (Synth PType m (Pos Expr) -> Synth NType m (Neg Expr)) -> Synth NType m (Neg Expr)
v >>- b = Synth $ do
  v' ::: _V <- synth v
  d <- depth
  let var = Synth $ do
        d' <- depth
        pure $ varE (Free (levelToIndex d' d)) ::: _V
  b' ::: _T <- Binding __ Many (STerm _V) |- synth (b var)
  pure $ bindE v' b' ::: _T

infixl 1 >>-


-- General combinators

instantiate :: Algebra sig m => (a -> TExpr -> a) -> a ::: Type -> Elab m (a ::: Type)
instantiate inst = go
  where
  go (e ::: _T) = case _T of
    ForAll _ _T _B -> do
      m <- meta _T
      go (inst e (TVar (Metavar m)) ::: _B (metavar m))
    _              -> pure $ e ::: _T

hole :: (HasCallStack, Has (Throw Err) sig m) => Name -> Check PType m a
hole n = Check $ \ _T -> withFrozenCallStack $ err $ Hole n _T

switch :: (HasCallStack, Has (Throw Err) sig m) => Synth Type m a -> Check Type m a
switch (Synth m) = Check $ \ _K -> m >>= \ (a ::: _K') -> a <$ unify _K' _K

as :: (HasCallStack, Has (Throw Err) sig m) => Check Type m a ::: IsType m TExpr -> Synth Type m a
as (m ::: _T) = Synth $ do
  env <- views context_ toEnv
  subst <- get
  _T' <- T.eval subst (Left <$> env) <$> checkIsType (_T ::: Type)
  a <- check (m ::: _T')
  pure $ a ::: _T'


-- Pattern combinators

wildcardP :: Bind m (ValuePattern Name)
wildcardP = Bind $ \ _ _ -> fmap (PWildcard,)

varP :: (HasCallStack, Has (Throw Err) sig m) => Name -> Bind m (ValuePattern Name)
varP n = Bind $ \ q _A b -> Check $ \ _B -> (PVar n,) <$> (Binding n q (STerm _A) |- check (b ::: _B))

conP :: (HasCallStack, Has (Throw Err) sig m) => QName -> [Bind m (ValuePattern Name)] -> Bind m (ValuePattern Name)
conP n ps = Bind $ \ q _A b -> Check $ \ _B -> do
  n' :=: _ ::: _T <- traverse (instantiate const . forcing) =<< resolveC n
  (ps', b') <- check (bind (fieldsP (Bind (\ _q' _A' b -> ([],) <$> Check (\ _B -> unify (returnOf _A') _A *> check (b ::: _B)))) ps ::: (q, _T)) b ::: _B)
  pure (PCon n' (fromList ps'), b')
  where
  -- FIXME: this feels a bit gross, but we have to accommodate both nullary (already data) and non-nullary (thunk (args… -> comp data)) constructors.
  returnOf = \case{ Comp [] _T -> _T ; _T -> _T }
  forcing (e ::: Pos _T) = case _T of
    Thunk _T -> e ::: _T
    _        -> e ::: _T

fieldsP :: (HasCallStack, Has (Throw Err) sig m) => Bind m [a] -> [Bind m a] -> Bind m [a]
fieldsP = foldr cons
  where
  cons p ps = Bind $ \ q _A b -> Check $ \ _B -> do
    (_ ::: (q', _A'), _A'') <- expectFunction "when checking nested pattern" _A
    (p', (ps', b')) <- check (bind (p ::: (q', _A')) (bind (ps ::: (q, _A'')) b) ::: _B)
    pure (p':ps', b')


allP :: (HasCallStack, Has (Throw Err) sig m) => Name -> Bind m (EffectPattern Name)
allP n = Bind $ \ q _A b -> Check $ \ _B -> do
  (sig, _A') <- expectComp "when checking catch-all pattern" =<< expectThunk "when checking catch-all pattern" _A
  (PAll n,) <$> (Binding n q (STerm (Thunk (Comp sig _A'))) |- check (b ::: _B))

effP :: (HasCallStack, Has (Throw Err) sig m) => QName -> [Bind m (ValuePattern Name)] -> Name -> Bind m (Pattern Name)
effP n ps v = Bind $ \ q _A b -> Check $ \ _B -> do
  StaticContext{ module', graph } <- ask
  (sig, _A') <- expectComp "when checking effect pattern" =<< expectThunk "when checking effect pattern" _A
  n' ::: _T <- maybe (freeVariable n) (\ (n :=: _ ::: _T) -> instantiate const (n ::: getPos _T)) (traverse unDTerm =<< lookupInSig n module' graph sig)
  (ps', b') <- check (bind (fieldsP (Bind (\ q' _A' b -> ([],) <$> Check (\ _B -> Binding v q' (STerm (Thunk (Arrow Nothing Many _A' (Comp [] _A)))) |- check (b ::: _B)))) ps ::: (q, _T)) b ::: _B)
  pure (peff n' (fromList ps') v, b')


-- Expression elaboration

synthExprNeg :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> Synth NType m (Neg Expr)
synthExprNeg (S.Ann s _ e) = mapSynth (pushSpan s) $ case e of
  S.Var n    -> Synth (instantiate instE =<< synth (returnE <$> var n))
  S.Hole{}   -> nope
  S.Lam{}    -> nope
  S.App f a  -> app (synthExprNeg f) (checkExprPos a)
  S.As t _T  -> as (checkExprNeg t ::: getPos <$> elabType _T)
  S.String s -> returnE <$> string s
  where
  nope = Synth $ couldNotSynthesize (show e)

synthExprPos :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> Synth PType m (Pos Expr)
synthExprPos (S.Ann s _ e) = mapSynth (pushSpan s) $ case e of
  S.Var n    -> var n
  S.Hole{}   -> nope
  S.Lam{}    -> nope
  S.App{}    -> nope
  S.As t _T  -> as (checkExprPos t ::: getPos <$> elabType _T)
  S.String s -> string s
  where
  nope = Synth $ couldNotSynthesize (show e)


checkExprNeg :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> Check NType m (Neg Expr)
checkExprNeg expr@(S.Ann s _ e) = mapCheck (pushSpan s) $ case e of
  S.Var{}    -> synth
  S.Hole n   -> hole n
  S.Lam cs   -> returnE <$> lam (map (\ (S.Clause p b) -> (bindPattern p, checkExprNeg b)) cs)
  S.App{}    -> synth
  S.As{}     -> synth
  S.String{} -> synth
  where
  synth = switch (synthExprNeg expr)

checkExprPos :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> Check PType m (Pos Expr)
checkExprPos expr@(S.Ann s _ e) = mapCheck (pushSpan s) $ case e of
  S.Var{}    -> synth
  S.Hole n   -> hole n
  S.Lam cs   -> lam (map (\ (S.Clause p b) -> (bindPattern p, checkExprNeg b)) cs)
  S.App{}    -> synth
  S.As{}     -> synth
  S.String{} -> synth
  where
  synth = switch (synthExprPos expr)


-- FIXME: check for unique variable names
bindPattern :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Pattern -> Bind m (Pattern Name)
bindPattern = go where
  go = withSpanB $ \case
    S.PVal p -> Bind $ \ q _T -> bind (PVal <$> goVal p ::: (q, maybe _T snd (unComp =<< unThunk _T)))
    S.PEff p -> withSpanB (\ (S.POp n ps v) -> effP n (map goVal ps) v) p

  goVal = withSpanB $ \case
    S.PWildcard -> wildcardP
    S.PVar n    -> varP n
    S.PCon n ps -> conP n (map goVal ps)


-- | Elaborate a type abstracted over another type’s parameters.
--
-- This is used to elaborate data constructors & effect operations, which receive the type/interface parameters as implicit parameters ahead of their own explicit ones.
abstractType :: (HasCallStack, Has (Throw Err) sig m) => IsType m (Pos TExpr) -> Kind -> Elab m (Pos TExpr)
abstractType body = go
  where
  go = \case
    KArrow (Just n) a b -> thunkT . forAllT n a . compT [] <$> (Binding n zero (SType a) |- go b)
    _                   -> checkIsType (body ::: Type)

abstractTerm :: (HasCallStack, Has (Throw Err) sig m) => (Snoc TExpr -> Snoc (Pos Expr) -> Pos Expr) -> Check PType m (Pos Expr)
abstractTerm body = go Nil Nil
  where
  go ts fs = Check $ \case
    ForAll n                  _T   _B -> do
      d <- depth
      check (tlam (returnE <$> go (ts :> d) fs) ::: ForAll n _T _B)
    Arrow  n q (Thunk (Comp s _A)) _B -> do
      d <- depth
      check (lam [(PEff <$> allP (fromMaybe __ n), returnE <$> go ts (fs :> d))] ::: Arrow n q (Thunk (Comp s _A)) _B)
    Arrow  n q                _A   _B -> do
      d <- depth
      check (lam [(PVal <$> varP (fromMaybe __ n), returnE <$> go ts (fs :> d))] ::: Arrow n q _A _B)
    _T                                -> do
      d <- depth
      pure $ body (TVar . Free . levelToIndex d <$> ts) (varE . Free . levelToIndex d <$> fs)


-- Declarations

elabDataDef
  :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source :+: Throw Err) sig m)
  => Name ::: Kind
  -> [S.Ann (Name ::: S.Ann S.Type)]
  -> m [Name :=: Def]
-- FIXME: check that all constructors return the datatype.
elabDataDef (dname ::: _T) constructors = do
  mname <- view name_
  cs <- for constructors $ \ (S.Ann s _ (n ::: t)) -> do
    c_T <- runElabType $ pushSpan (S.ann t) $ getPos <$> abstractType (elabType t) _T
    con' <- runElabTerm $ pushSpan s $ check (abstractTerm (conE (mname :.: n)) ::: c_T)
    pure $ n :=: DTerm (Just con') (Pos c_T)
  pure
    $ (dname :=: DData (scopeFromList cs) _T)
    : cs


elabInterfaceDef
  :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source :+: Throw Err) sig m)
  => Name ::: Kind
  -> [S.Ann (Name ::: S.Ann S.Type)]
  -> m [Name :=: Def]
elabInterfaceDef (dname ::: _T) constructors = do
  mname <- view name_
  cs <- for constructors $ \ (S.Ann s _ (n ::: t)) -> do
    _T' <- runElabType $ pushSpan (S.ann t) $ getPos <$> abstractType (elabType t) _T
    -- FIXME: check that the interface is a member of the sig.
    op' <- runElabTerm $ pushSpan s $ check (abstractTerm (\ ts fs -> thunkE (opE (mname :.: n) ts fs)) ::: _T')
    pure $ n :=: DTerm (Just op') (Pos _T')
  pure [ dname :=: DInterface (scopeFromList cs) _T ]


elabTermDef
  :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source :+: Throw Err :+: Write Warn) sig m)
  => Type
  -> S.Ann S.Expr
  -> m (Pos Expr)
-- FIXME: this is wrong; we shouldn’t just indiscriminately thunk everything
elabTermDef _T expr@(S.Ann s _ _) = runElabTerm $ pushSpan s $ thunkE <$> check (bind (checkExprNeg expr) ::: _T)
  where
  -- bind :: Check Type m (Neg Expr) -> Check Type m (Neg Expr)
  bind k = Check $ \ _T -> case _T of
    Thunk ForAll{}                                  -> returnE <$> check (tlam (bind k) ::: _T)
    Thunk (Arrow (Just n) q (Thunk (Comp s _A)) _B) -> returnE <$> check (lam [(PEff <$> allP n, bind k)] ::: Thunk (Arrow Nothing q (Thunk (Comp s _A)) _B))
    Thunk (Arrow (Just n) q                _A   _B) -> returnE <$> check (lam [(PVal <$> varP n, bind k)] ::: Thunk (Arrow Nothing q _A _B))
    -- FIXME: this doesn’t do what we want for tacit definitions, i.e. where _T is itself a telescope.
    -- FIXME: eta-expanding here doesn’t help either because it doesn’t change the way elaboration of the surface term occurs.
    -- we’ve exhausted the named parameters; the rest is up to the body.
    _                                               -> check (k ::: _T)


-- Modules

elabModule
  :: (HasCallStack, Has (Reader Graph :+: Reader Source :+: Throw Err :+: Write Warn) sig m)
  => S.Ann S.Module
  -> m Module
elabModule (S.Ann _ _ (S.Module mname is os ds)) = execState (Module mname [] os mempty) $ do
  let (importedNames, imports) = mapAccumL (\ names (S.Ann _ _ S.Import{ name }) -> (Set.insert name names, Import name)) Set.empty is
  imports_ .= imports

  local (`restrict` importedNames) $ do
    -- FIXME: maybe figure out the graph for mutual recursion?
    -- FIXME: check for redundant naming

    -- elaborate all the types first
    es <- for ds $ \ (S.Ann _ _ (dname, S.Ann _ _ (S.Decl ty def))) -> case def of
      S.TypeDef k cs -> Nothing <$ do
        _T <- runModule $ runElabKind $ checkIsType (elabKind ty ::: Type)
        let (cons, elab) = case k of
              S.DataDef      -> (DData,      elabDataDef)
              S.InterfaceDef -> (DInterface, elabInterfaceDef)
        scope_.decls_.at dname .= Just (cons mempty _T)
        decls <- runModule $ elab (dname ::: _T) cs
        for_ decls $ \ (dname :=: decl) -> scope_.decls_.at dname .= Just decl

      S.TermDef t -> do
        _T <- runModule $ runElabType $ getPos <$> checkIsType (elabType ty ::: Type)
        scope_.decls_.at dname .= Just (DTerm Nothing (Pos _T))
        pure (Just (dname, t ::: _T))

    -- then elaborate the terms
    for_ (catMaybes es) $ \ (dname, t ::: _T) -> do
      t' <- runModule $ elabTermDef _T t
      scope_.decls_.ix dname .= DTerm (Just t') (Pos _T)


-- Errors

-- FIXME: rename all the expect* actions to assert*.
-- FIXME: can we get away without the extra message?
-- FIXME: can we replace these by unification? Maybe not if we want to get names and quantities out?
expectQuantifier :: (HasCallStack, Has (Throw Err) sig m) => String -> NType -> Elab m (Name ::: Kind, PType -> NType)
expectQuantifier = expectType (\case{ ForAll n t b -> pure (n ::: t, b) ; _ -> Nothing }) "{_} -> _"

expectFunction :: (HasCallStack, Has (Throw Err) sig m) => String -> NType -> Elab m (Maybe Name ::: (Quantity, PType), NType)
expectFunction = expectType (\case{ Arrow n q t b -> pure (n ::: (q, t), b) ; _ -> Nothing }) "_ -> _"

-- | Expect a tacit (non-variable-binding) function type.
expectTacitFunction :: (HasCallStack, Has (Throw Err) sig m) => String -> NType -> Elab m ((Quantity, PType), NType)
expectTacitFunction = expectType (\case{ Arrow Nothing q t b -> pure ((q, t), b) ; _ -> Nothing }) "_ -> _"

-- | Expect a computation type with effects.
expectComp :: (HasCallStack, Has (Throw Err) sig m) => String -> NType -> Elab m ([Interface], PType)
expectComp = expectType (\case{ Comp s t -> pure (s, t) ; _ -> Nothing }) "[_] _"

-- | Expect a value type wrapping a computation.
expectThunk :: (HasCallStack, Has (Throw Err) sig m) => String -> PType -> Elab m NType
expectThunk = expectType unThunk "thunk _"


-- Elaboration

runModule :: Has (State Module) sig m => ReaderC Module m a -> m a
runModule m = do
  mod <- get
  runReader mod m

withSpanB :: Algebra sig m => (a -> Bind m b) -> S.Ann a -> Bind m b
withSpanB k (S.Ann s _ a) = mapBind (pushSpan s) (k a)

extendSigFor :: Has (Reader ElabContext) sig m => NType -> m a -> m a
extendSigFor _T m = case _T of
  Comp sig _ -> locally sig_ (++ sig) m
  _          -> m


-- Judgements

check :: Algebra sig m => (Check Type m a ::: Type) -> Elab m a
check (m ::: _T) = extendSigFor _T $ runCheck m _T

newtype Check t m a = Check { runCheck :: t -> Elab m a }
  deriving (Applicative, Functor) via ReaderC t (Elab m)

mapCheck :: (Elab m a -> Elab m b) -> Check t m a -> Check t m b
mapCheck f m = Check $ \ _T -> f (runCheck m _T)


newtype Synth t m a = Synth { synth :: Elab m (a ::: t) }

instance Functor (Synth t m) where
  fmap f (Synth m) = Synth (first f <$> m)

mapSynth :: (Elab m (a ::: t) -> Elab m (b ::: u)) -> Synth t m a -> Synth u m b
mapSynth f = Synth . f . synth


bind :: Bind m a ::: (Quantity, Type) -> Check Type m b -> Check Type m (a, b)
bind (p ::: (q, _T)) = runBind p q _T

newtype Bind m a = Bind { runBind :: forall x . Quantity -> Type -> Check Type m x -> Check Type m (a, x) }
  deriving (Functor)

mapBind :: (forall x . Elab m (a, x) -> Elab m (b, x)) -> Bind m a -> Bind m b
mapBind f m = Bind $ \ q _A b -> mapCheck f (runBind m q _A b)
