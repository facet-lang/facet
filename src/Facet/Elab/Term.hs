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
, holeN
, holeP
, switchN
, switchP
, asN
, asP
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
global :: QName ::: PType -> Synth PType m PExpr
global (q ::: _T) = Synth $ pure $ varE (Global q) ::: _T

-- FIXME: do we need to instantiate here to deal with rank-n applications?
-- FIXME: effect ops not in the sig are reported as not in scope
-- FIXME: effect ops in the sig are available whether or not they’re in scope
var :: (HasCallStack, Has (Throw Err) sig m) => QName -> Synth PType m PExpr
var n = Synth $ ask >>= \ StaticContext{ module', graph } -> ask >>= \ ElabContext{ context, sig } -> if
  | Just (i, q, STerm _T) <- lookupInContext n context                      -> use i q $> (varE (Free i) ::: _T)
  | Just (_ :=: DTerm (Just x) _T) <- lookupInSig n module' graph sig -> pure (x ::: _T)
  | otherwise                                                         -> do
    n :=: d <- resolveQ n
    _T <- case d of
      DTerm _ _T -> pure _T
      _          -> freeVariable n
    synth $ global (n ::: _T)


-- | Elaborate a thunked type lambda from its body.
tlam :: (HasCallStack, Has (Throw Err) sig m) => Check PType m PExpr -> Check PType m PExpr
tlam b = Check $ \ _T -> do
  (n ::: _A, _B) <- assertQuantifier _T
  d <- depth
  b' <- Binding n zero (SType _A) |- check (b ::: _B (free d))
  pure $ tlamE b'

-- | Elaborate a thunked lambda from its clauses.
lam :: (HasCallStack, Has (Throw Err) sig m) => [(Bind PType m (Pattern Name), Check NType m NExpr)] -> Check NType m NExpr
lam cs = Check $ \ _T -> do
  (_A, _B) <- assertTacitFunction _T
  lamE <$> traverse (\ (p, b) -> check (bind (p ::: _A) b ::: _B)) cs


app :: (HasCallStack, Has (Throw Err) sig m) => Synth NType m NExpr -> Check PType m PExpr -> Synth NType m NExpr
app f a = Synth $ do
  f' ::: _F <- synth f
  (_ ::: (q, _A), _B) <- assertFunction _F
  a' <- censor @Usage (q ><<) $ extendSigFor _A $ check (a ::: _A)
  pure $ appE f' a' ::: _B


string :: Text -> Synth PType m PExpr
string s = Synth $ pure $ stringE s ::: T.String


-- Polarity shifts

force :: (HasCallStack, Has (Throw Err) sig m) => Synth PType m PExpr -> Synth NType m NExpr
force t = Synth $ do
  t' ::: _T <- synth t
  -- FIXME: assert by unification
  _T' <- assertThunk _T
  pure $ forceE t' ::: _T'

thunk :: (HasCallStack, Has (Throw Err) sig m) => Check NType m NExpr -> Check PType m PExpr
thunk c = Check $ fmap thunkE . check . (c :::) <=< assertThunk

return' :: Algebra sig m => Synth PType m PExpr -> Synth NType m NExpr
return' v = Synth $ do
  v' ::: _V <- synth v
  sig <- view sig_
  pure $ returnE v' ::: Comp sig _V

(>>-) :: Has (Throw Err) sig m => Synth NType m NExpr -> (Synth PType m PExpr -> Synth NType m NExpr) -> Synth NType m NExpr
v >>- b = Synth $ do
  v' ::: _FV <- synth v
  (_, _V) <- assertComp _FV
  d <- depth
  let var = Synth $ do
        d' <- depth
        pure $ varE (Free (levelToIndex d' d)) ::: _V
  b' ::: _T <- Binding __ Many (STerm _V) |- synth (b var)
  pure $ bindE v' b' ::: _T

infixl 1 >>-


-- General combinators

instantiate :: Algebra sig m => (a -> PTExpr -> a) -> a ::: PType -> Elab m (a ::: PType)
instantiate inst = go
  where
  go (e ::: _T) = case _T of
    ForAll _ _T _B -> do
      m <- meta _T
      go (inst e (TVar (Metavar m)) ::: _B (metavar m))
    _                      -> pure $ e ::: _T

holeN :: (HasCallStack, Has (Throw Err) sig m) => Name -> Check NType m a
holeN n = Check $ \ _T -> withFrozenCallStack $ err $ Hole n (EN _T)

holeP :: (HasCallStack, Has (Throw Err) sig m) => Name -> Check PType m a
holeP n = Check $ \ _T -> withFrozenCallStack $ err $ Hole n (EP _T)

switchN :: (HasCallStack, Has (Throw Err) sig m) => Synth NType m a -> Check NType m a
switchN (Synth m) = Check $ \ _K -> m >>= \ (a ::: _K') -> a <$ unifyN _K' _K

switchP :: (HasCallStack, Has (Throw Err) sig m) => Synth PType m a -> Check PType m a
switchP (Synth m) = Check $ \ _K -> m >>= \ (a ::: _K') -> a <$ unifyP _K' _K

asN :: (HasCallStack, Has (Throw Err) sig m) => Check NType m a ::: IsType m NTExpr -> Synth NType m a
asN (m ::: _T) = Synth $ do
  env <- views context_ toEnv
  subst <- get
  _T' <- T.evalN subst (Left <$> env) <$> checkIsType (_T ::: Type)
  a <- check (m ::: _T')
  pure $ a ::: _T'

asP :: (HasCallStack, Has (Throw Err) sig m) => Check PType m a ::: IsType m PTExpr -> Synth PType m a
asP (m ::: _T) = Synth $ do
  env <- views context_ toEnv
  subst <- get
  _T' <- T.evalP subst (Left <$> env) <$> checkIsType (_T ::: Type)
  a <- check (m ::: _T')
  pure $ a ::: _T'


-- Pattern combinators

wildcardP :: Bind PType m (ValuePattern Name)
wildcardP = Bind $ \ _ _ -> fmap (PWildcard,)

varP :: (HasCallStack, Has (Throw Err) sig m) => Name -> Bind PType m (ValuePattern Name)
varP n = Bind $ \ q _A b -> Check $ \ _B -> (PVar n,) <$> (Binding n q (STerm _A) |- check (b ::: _B))

conP :: (HasCallStack, Has (Throw Err) sig m) => QName -> [Bind PType m (ValuePattern Name)] -> Bind PType m (ValuePattern Name)
conP n ps = Bind $ \ q _A b -> Check $ \ _B -> do
  n' :=: _ ::: _T <- traverse (instantiate const) =<< resolveC n
  (ps', b') <- check (bind (fieldsP (Bind (\ _q' _A' b -> ([],) <$> Check (\ _B -> unifyP (returnOf _A') _A *> check (b ::: _B)))) ps ::: (q, _T)) b ::: _B)
  pure (PCon n' (fromList ps'), b')
  where
  -- FIXME: this feels a bit gross, but we have to accommodate both nullary (already data) and non-nullary (thunk (args… -> comp data)) constructors.
  returnOf = \case{ Thunk (Comp [] _T) -> _T ; _T -> _T }

fieldsP :: (HasCallStack, Has (Throw Err) sig m) => Bind PType m [a] -> [Bind PType m a] -> Bind PType m [a]
fieldsP = foldr cons
  where
  cons p ps = Bind $ \ q _A b -> Check $ \ _B -> do
    (_ ::: (q', _A'), _A'') <- assertFunction =<< assertThunk _A
    (_, _A''') <- assertComp _A''
    (p', (ps', b')) <- check (bind (p ::: (q', _A')) (bind (ps ::: (q, _A''')) b) ::: _B)
    pure (p':ps', b')


allP :: (HasCallStack, Has (Throw Err) sig m) => Name -> Bind PType m (EffectPattern Name)
allP n = Bind $ \ q _A b -> Check $ \ _B -> do
  (sig, _A') <- assertComp =<< assertThunk _A
  (PAll n,) <$> (Binding n q (STerm (Thunk (Comp sig _A'))) |- check (b ::: _B))

op :: (HasCallStack, Has (Throw Err) sig m) => [Interface] -> QName -> Synth PType m QName
op sig n = Synth $ do
  StaticContext{ module', graph } <- ask
  maybe (freeVariable n) (instantiate const . ((:::) <$> nm <*> ty . def)) (traverse unDTerm =<< lookupInSig n module' graph sig)

effP :: (HasCallStack, Has (Throw Err) sig m) => QName -> [Bind PType m (ValuePattern Name)] -> Name -> Bind PType m (Pattern Name)
effP n ps v = Bind $ \ q _A b -> Check $ \ _B -> do
  (sig, _A') <- assertComp =<< assertThunk _A
  n' ::: _T <- synth (op sig n)
  (ps', b') <- check (bind (fieldsP (Bind (\ q' _A' b -> ([],) <$> Check (\ _B -> Binding v q' (STerm (Thunk (Arrow Nothing Many _A' (Comp [] _A)))) |- check (b ::: _B)))) ps ::: (q, _T)) b ::: _B)
  pure (peff n' (fromList ps') v, b')


-- Expression elaboration

synthExprNeg :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> Synth NType m NExpr
synthExprNeg expr@(S.Ann s _ e) = mapSynth (pushSpan s) $ case e of
  S.Var{}    -> return' (synthExprPos expr)
  S.Hole{}   -> nope
  S.Lam{}    -> nope
  S.App f a  -> synthExprNeg f >>- \ f' -> Synth (do{ _ ::: _F <- synth f'; (_ ::: (_, _A), _B) <- assertFunction =<< assertThunk _F; a' <- check (checkExprNeg a ::: Comp [] _A) ; pure (a' ::: Comp [] _A) }) >>- \ a' -> app (force f') (switchP a')
  S.As t _T  -> asN (checkExprNeg t ::: elabNType _T)
  S.String{} -> return' (synthExprPos expr)
  where
  nope = Synth $ couldNotSynthesize (show e)

synthExprPos :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> Synth PType m PExpr
synthExprPos (S.Ann s _ e) = mapSynth (pushSpan s) $ case e of
  S.Var n    -> Synth (instantiate instE =<< synth (var n))
  S.Hole{}   -> nope
  S.Lam{}    -> nope
  S.App{}    -> nope
  S.As t _T  -> asP (checkExprPos t ::: elabPType _T)
  S.String s -> string s
  where
  nope = Synth $ couldNotSynthesize (show e)


checkExprNeg :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> Check NType m NExpr
checkExprNeg expr@(S.Ann s _ e) = mapCheck (pushSpan s) $ case e of
  S.Var{}    -> synth
  S.Hole n   -> holeN n
  S.Lam cs   -> lam (map (\ (S.Clause p b) -> (bindPattern p, checkExprNeg b)) cs)
  S.App{}    -> synth
  S.As{}     -> synth
  S.String{} -> synth
  where
  synth = switchN (synthExprNeg expr)

checkExprPos :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> Check PType m PExpr
checkExprPos expr@(S.Ann s _ e) = mapCheck (pushSpan s) $ case e of
  S.Var{}    -> synth
  S.Hole n   -> holeP n
  S.Lam cs   -> thunk (lam (map (\ (S.Clause p b) -> (bindPattern p, checkExprNeg b)) cs))
  S.App{}    -> synth
  S.As{}     -> synth
  S.String{} -> synth
  where
  synth = switchP (synthExprPos expr)


-- FIXME: check for unique variable names
bindPattern :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Pattern -> Bind PType m (Pattern Name)
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
abstractType :: (HasCallStack, Has (Throw Err) sig m) => IsType m PTExpr -> Kind -> Elab m PTExpr
abstractType body = go
  where
  go = \case
    KArrow (Just n) a b -> TForAll n a <$> (Binding n zero (SType a) |- go b)
    _                   -> checkIsType (body ::: Type)

abstractTerm :: (HasCallStack, Has (Throw Err) sig m) => (Snoc PTExpr -> Snoc PExpr -> Pos Expr) -> Check PType m PExpr
abstractTerm body = go Nil Nil
  where
  go ts fs = Check $ \case
    ForAll n          _T _B  -> do
      d <- depth
      check (tlam (go (ts :> d) fs) ::: ForAll n _T _B)
    Thunk (Arrow  n q _A _B) -> do
      d <- depth
      check (thunk (lam [(patFor _A (fromMaybe __ n), shift (go ts (fs :> d)))]) ::: Thunk (Arrow n q _A _B))
    _T                       -> do
      d <- depth
      pure $ body (TVar . Free . levelToIndex d <$> ts) (varE . Free . levelToIndex d <$> fs)
  shift e = Check (\ _T -> do
    (_, _T') <- assertComp _T
    returnE <$> check (e ::: _T'))

patFor :: (HasCallStack, Has (Throw Err) sig m) => PType -> Name -> Bind PType m (Pattern Name)
patFor = \case{ Thunk Comp{} -> fmap PEff . allP ; _ -> fmap PVal . varP }


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
    c_T <- runElabType $ pushSpan (S.ann t) $ abstractType (elabPType t) _T
    con' <- runElabTerm $ pushSpan s $ check (abstractTerm (conE (mname :.: n)) ::: c_T)
    pure $ n :=: DTerm (Just con') c_T
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
    _T' <- runElabType $ pushSpan (S.ann t) $ abstractType (elabPType t) _T
    -- FIXME: check that the interface is a member of the sig.
    op' <- runElabTerm $ pushSpan s $ check (abstractTerm (\ ts fs -> thunkE (opE (mname :.: n) ts fs)) ::: _T')
    pure $ n :=: DTerm (Just op') _T'
  pure [ dname :=: DInterface (scopeFromList cs) _T ]


elabTermDef
  :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source :+: Throw Err :+: Write Warn) sig m)
  => PType
  -> S.Ann S.Expr
  -> m PExpr
elabTermDef _T expr@(S.Ann s _ _) = runElabTerm $ pushSpan s $ either id id <$> check (bind (checkExprNeg expr) ::: _T)
  where
  bind k = Check $ \case
    _T@ForAll{}                    -> Right <$> check (tlam (either id id <$> bind k) ::: _T)
    Thunk (Arrow (Just n) q _A _B) -> Right <$> check (thunk (lam [(patFor _A n, shift (bind k))]) ::: Thunk (Arrow Nothing q _A _B))
    -- FIXME: this doesn’t do what we want for tacit definitions, i.e. where _T is itself a telescope.
    -- FIXME: eta-expanding here doesn’t help either because it doesn’t change the way elaboration of the surface term occurs.
    -- we’ve exhausted the named parameters; the rest is up to the body.
    _T                             -> Left <$> check (thunk k ::: _T)
  shift e = Check (\ _T -> do
    (_, _T') <- assertComp _T
    either forceE returnE <$> check (e ::: _T'))


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
        _T <- runModule $ runElabType $ checkIsType (elabPType ty ::: Type)
        scope_.decls_.at dname .= Just (DTerm Nothing _T)
        pure (Just (dname, t ::: _T))

    -- then elaborate the terms
    for_ (catMaybes es) $ \ (dname, t ::: _T) -> do
      t' <- runModule $ elabTermDef _T t
      scope_.decls_.ix dname .= DTerm (Just t') _T


-- Errors

-- FIXME: can we get away without the extra message?
-- FIXME: can we replace these by unification? Maybe not if we want to get names and quantities out?
assertQuantifier :: (HasCallStack, Has (Throw Err) sig m) => PType -> Elab m (Name ::: Kind, PType -> PType)
assertQuantifier = assertPType (\case{ ForAll n t b -> pure (n ::: t, b) ; _ -> Nothing }) "{_} -> _"

assertFunction :: (HasCallStack, Has (Throw Err) sig m) => NType -> Elab m (Maybe Name ::: (Quantity, PType), NType)
assertFunction = assertNType (\case{ Arrow n q t b -> pure (n ::: (q, t), b) ; _ -> Nothing }) "_ -> _"

-- | Expect a tacit (non-variable-binding) function type.
assertTacitFunction :: (HasCallStack, Has (Throw Err) sig m) => NType -> Elab m ((Quantity, PType), NType)
assertTacitFunction = assertNType (\case{ Arrow Nothing q t b -> pure ((q, t), b) ; _ -> Nothing }) "_ -> _"

-- | Expect a computation type with effects.
assertComp :: (HasCallStack, Has (Throw Err) sig m) => NType -> Elab m ([Interface], PType)
assertComp = assertNType (\case{ Comp s t -> pure (s, t) ; _ -> Nothing }) "[_] _"

-- | Expect a value type wrapping a computation.
assertThunk :: (HasCallStack, Has (Throw Err) sig m) => PType -> Elab m NType
assertThunk = assertPType unThunk "thunk _"


-- Elaboration

runModule :: Has (State Module) sig m => ReaderC Module m a -> m a
runModule m = do
  mod <- get
  runReader mod m

withSpanB :: Algebra sig m => (a -> Bind t m b) -> S.Ann a -> Bind t m b
withSpanB k (S.Ann s _ a) = mapBind (pushSpan s) (k a)

extendSigFor :: Has (Reader ElabContext) sig m => PType -> m a -> m a
extendSigFor = \case
  Thunk (Comp sig _) -> locally sig_ (++ sig)
  _                  -> id


-- Judgements

check :: (Check t m a ::: t) -> Elab m a
check (m ::: _T) = runCheck m _T

newtype Check t m a = Check { runCheck :: t -> Elab m a }
  deriving (Applicative, Functor) via ReaderC t (Elab m)

mapCheck :: (Elab m a -> Elab m b) -> Check t m a -> Check t m b
mapCheck f m = Check $ \ _T -> f (runCheck m _T)


newtype Synth t m a = Synth { synth :: Elab m (a ::: t) }

instance Functor (Synth t m) where
  fmap f (Synth m) = Synth (first f <$> m)

mapSynth :: (Elab m (a ::: t) -> Elab m (b ::: u)) -> Synth t m a -> Synth u m b
mapSynth f = Synth . f . synth


bind :: Bind t m a ::: (Quantity, t) -> Check NType m b -> Check NType m (a, b)
bind (p ::: (q, _T)) = runBind p q _T

newtype Bind t m a = Bind { runBind :: forall x . Quantity -> t -> Check NType m x -> Check NType m (a, x) }
  deriving (Functor)

mapBind :: (forall x . Elab m (a, x) -> Elab m (b, x)) -> Bind t m a -> Bind t m b
mapBind f m = Bind $ \ q _A b -> mapCheck f (runBind m q _A b)
