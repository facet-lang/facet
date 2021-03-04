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
  -- * Pattern combinators
, wildcardP
, varP
, conP
, fieldsP
, allP
, effP
  -- * Expression elaboration
, synthExpr
, synthExprNeg
, synthExprPos
, checkExpr
, checkExprNeg
, checkExprPos
, bindPattern
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
import           Control.Effect.Lens (view, (.=))
import           Control.Effect.Throw
import           Control.Effect.Writer
import           Control.Lens (at, ix)
import           Control.Monad ((<=<))
import           Data.Foldable
import           Data.Functor
import           Data.Maybe (catMaybes, fromMaybe)
import qualified Data.Set as Set
import           Data.Text (Text)
import           Data.Traversable (for, mapAccumL)
import           Facet.Context (Binding(..))
import           Facet.Core.Module as Module
import           Facet.Core.Term as E
import           Facet.Core.Type as T hiding (global)
import           Facet.Effect.Write
import           Facet.Elab
import           Facet.Elab.Type
import           Facet.Graph
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
global :: QName ::: Type -> Synth m (Pos Expr)
global (q ::: _T) = Synth $ pure $ varE (Global q) ::: _T

-- FIXME: do we need to instantiate here to deal with rank-n applications?
-- FIXME: effect ops not in the sig are reported as not in scope
-- FIXME: effect ops in the sig are available whether or not they’re in scope
var :: (HasCallStack, Has (Throw Err) sig m) => QName -> Synth m (Pos Expr)
var n = Synth $ ask >>= \ StaticContext{ module', graph } -> ask >>= \ ElabContext{ context, sig } -> if
  | Just (i, q, _T) <- lookupInContext n context                      -> use i q $> (varE (Free i) ::: _T)
  | Just (_ :=: DTerm (Just x) _T) <- lookupInSig n module' graph sig -> pure (x ::: getPos _T)
  | otherwise                                                         -> do
    n :=: d <- resolveQ n
    _T <- case d of
      DTerm _ _T -> pure _T
      _          -> freeVariable n
    synth $ global (n ::: getPos _T)


tlam :: (HasCallStack, Has (Throw Err) sig m) => Check m (Neg Expr) -> Check m (Neg Expr)
tlam b = Check $ \ _T -> do
  (n ::: _A, _B) <- expectQuantifier "when checking type abstraction" _T
  d <- depth
  b' <- Binding n zero _A |- check (b ::: _B (free d))
  pure $ tlamE b'

lam :: (HasCallStack, Has (Throw Err) sig m) => [(Bind m (Pattern Name), Check m (Neg Expr))] -> Check m (Neg Expr)
lam cs = Check $ \ _T -> do
  (_A, _B) <- expectTacitFunction "when checking clause" _T
  lamE <$> traverse (\ (p, b) -> check (bind (p ::: _A) b ::: _B)) cs


app :: (HasCallStack, Has (Throw Err) sig m) => (a -> b -> c) -> Synth m a -> Check m b -> Synth m c
app mk f a = Synth $ do
  f' ::: _F <- synth f
  (_ ::: (q, _A), _B) <- expectFunction "in application" _F
  -- FIXME: test _A for Comp and extend the sig
  a' <- censor @Usage (q ><<) $ check (a ::: _A)
  pure $ mk f' a' ::: _B


string :: Text -> Synth m (Pos Expr)
string s = Synth $ pure $ stringE s ::: T.String


-- Polarity shifts

force :: Has (Throw Err) sig m => Check m (Pos Expr) -> Check m (Neg Expr)
force t = Check $ \ _T -> forceE <$> check (t ::: Thunk _T)

thunk :: (HasCallStack, Has (Throw Err) sig m) => Check m (Neg Expr) -> Check m (Pos Expr)
thunk c = Check $ fmap thunkE . check . (c :::) <=< expectThunk "when thunking computation"

(>>-) :: Has (Throw Err) sig m => Synth m (Neg Expr) -> (Synth m (Pos Expr) -> Synth m (Neg Expr)) -> Synth m (Neg Expr)
v >>- b = Synth $ do
  v' ::: _V <- synth v
  d <- depth
  let var = Synth $ do
        d' <- depth
        pure $ varE (Free (levelToIndex d' d)) ::: _V
  b' ::: _T <- Binding __ Many _V |- synth (b var)
  pure $ bindE v' b' ::: _T

infixl 1 >>-


-- Pattern combinators

wildcardP :: Bind m (ValuePattern Name)
wildcardP = Bind $ \ _ _ -> fmap (PWildcard,)

varP :: (HasCallStack, Has (Throw Err) sig m) => Name -> Bind m (ValuePattern Name)
varP n = Bind $ \ q _A b -> Check $ \ _B -> (PVar n,) <$> (Binding n q _A |- check (b ::: _B))

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
  (sig, _A') <- expectRet "when checking catch-all pattern" _A
  (PAll n,) <$> (Binding n q (Thunk (Comp sig _A')) |- check (b ::: _B))

effP :: (HasCallStack, Has (Throw Err) sig m) => QName -> [Bind m (ValuePattern Name)] -> Name -> Bind m (Pattern Name)
effP n ps v = Bind $ \ q _A b -> Check $ \ _B -> do
  StaticContext{ module', graph } <- ask
  (sig, _A') <- expectRet "when checking effect pattern" _A
  n' ::: _T <- maybe (freeVariable n) (\ (n :=: _ ::: _T) -> instantiate const (n ::: _T)) (traverse unDData =<< lookupInSig n module' graph sig)
  (ps', b') <- check (bind (fieldsP (Bind (\ q' _A' b -> ([],) <$> Check (\ _B -> Binding v q' (Thunk (Arrow Nothing Many _A' (Comp [] _A))) |- check (b ::: _B)))) ps ::: (q, _T)) b ::: _B)
  pure (peff n' (fromList ps') v, b')


-- Expression elaboration

synthExpr :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> Synth m (Either (Neg Expr) (Pos Expr))
synthExpr (S.Ann s _ e) = mapSynth (pushSpan s) $ case e of
  S.Var n    -> Left <$> Synth (instantiate instE . shiftNeg =<< synth (var n))
  S.Hole{}   -> nope
  S.Lam{}    -> nope
  S.App f a  -> Left <$> app appE (synthExprNeg f) (checkExprPos a)
  S.As t _T  -> as (checkExpr t ::: either getNeg getPos <$> switch (elabType _T))
  S.String s -> Right <$> string s
  where
  nope = Synth $ couldNotSynthesize (show e)

synthExprNeg :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> Synth m (Neg Expr)
synthExprNeg = Synth . fmap (\ (e ::: _T) -> either (::: _T) (shiftNeg . (::: _T)) e) . synth . synthExpr

synthExprPos :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> Synth m (Pos Expr)
synthExprPos = Synth . fmap (\ (e ::: _T) -> either (shiftPos . (::: _T)) (::: _T) e) . synth . synthExpr


checkExpr :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> Check m (Either (Neg Expr) (Pos Expr))
checkExpr expr@(S.Ann s _ e) = mapCheck (pushSpan s) $ case e of
  S.Var{}    -> synth
  S.Hole n   -> hole n
  S.Lam cs   -> Left <$> lam (map (\ (S.Clause p b) -> (bindPattern p, checkExprNeg b)) cs)
  S.App{}    -> synth
  S.As{}     -> synth
  S.String{} -> synth
  where
  synth = switch (synthExpr expr)

checkExprNeg :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> Check m (Neg Expr)
checkExprNeg expr = Check $ \ _T -> either id (tm . shiftNeg . (::: _T)) <$> check (checkExpr expr ::: _T)

checkExprPos :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> Check m (Pos Expr)
checkExprPos expr = Check $ \ _T -> either (tm . shiftPos . (::: _T)) id <$> check (checkExpr expr ::: _T)


shiftNeg :: Pos Expr ::: Type -> Neg Expr ::: Type
shiftNeg = \case
  v ::: Thunk _T -> forceE  v ::: _T
  v :::       _T -> returnE v ::: Comp [] _T

shiftPos :: Neg Expr ::: Type -> Pos Expr ::: Type
shiftPos (e ::: _T) = case unreturnE e ::: _T of
  -- FIXME: Is it ok to unwrap returns like this? Should we always just thunk it?
  Just v ::: Comp [] _T ->        v ::: _T
  _      :::         _T -> thunkE e ::: Thunk _T


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
abstractType :: (HasCallStack, Has (Throw Err) sig m) => Check m (Neg TExpr) -> Check m (Neg TExpr)
abstractType body = go
  where
  go = Check $ \case
    Arrow (Just n) _ a b -> do
      level <- depth
      b' <- Binding n zero a |- check (go ::: b)
      pure $ forAllT n (T.quote level a) b'
    _                    -> check (body ::: Type)

abstractTerm :: (HasCallStack, Has (Throw Err) sig m) => (Snoc TExpr -> Snoc (Pos Expr) -> Neg Expr) -> Check m (Neg Expr)
abstractTerm body = go Nil Nil
  where
  go ts fs = Check $ \case
    ForAll n                  _T   _B -> do
      d <- depth
      check (tlam (go (ts :> d) fs) ::: ForAll n _T _B)
    Arrow  n q (Thunk (Comp s _A)) _B -> do
      d <- depth
      check (lam [(PEff <$> allP (fromMaybe __ n), go ts (fs :> d))] ::: Arrow n q (Thunk (Comp s _A)) _B)
    Arrow  n q                _A   _B -> do
      d <- depth
      check (lam [(PVal <$> varP (fromMaybe __ n), go ts (fs :> d))] ::: Arrow n q _A _B)
    _T                                -> do
      d <- depth
      pure $ body (TVar . Free . levelToIndex d <$> ts) (varE . Free . levelToIndex d <$> fs)


-- Declarations

elabDataDef
  :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source :+: Throw Err) sig m)
  => Name ::: Type
  -> [S.Ann (Name ::: S.Ann S.Type)]
  -> m [Name :=: Def]
-- FIXME: check that all constructors return the datatype.
elabDataDef (dname ::: _T) constructors = do
  mname <- view name_
  cs <- for constructors $ \ (S.Ann s _ (n ::: t)) -> do
    c_T <- runElabType $ pushSpan (S.ann t) $ shiftPosTExpr . getNeg <$> check (abstractType (either id (compT []) <$> switch (elabType t)) ::: _T)
    con' <- runElabTerm $ pushSpan s $ check (thunk (abstractTerm (\ ts fs -> returnE (conE (mname :.: n) ts fs))) ::: c_T)
    pure $ n :=: DTerm (Just con') (Pos c_T)
  pure
    $ (dname :=: DData (scopeFromList cs) _T)
    : cs


elabInterfaceDef
  :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source :+: Throw Err) sig m)
  => Name ::: Type
  -> [S.Ann (Name ::: S.Ann S.Type)]
  -> m [Name :=: Def]
elabInterfaceDef (dname ::: _T) constructors = do
  mname <- view name_
  cs <- for constructors $ \ (S.Ann s _ (n ::: t)) -> do
    _T' <- runElabType $ pushSpan (S.ann t) $ shiftPosTExpr . getNeg <$> check (abstractType (either id (compT []) <$> switch (elabType t)) ::: _T)
    -- FIXME: check that the interface is a member of the sig.
    op' <- runElabTerm $ pushSpan s $ check (thunk (abstractTerm (opE (mname :.: n))) ::: _T')
    pure $ n :=: DTerm (Just op') (Pos _T')
  pure [ dname :=: DInterface (scopeFromList cs) _T ]


-- FIXME: add a parameter for the effect signature.
elabTermDef
  :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source :+: Throw Err :+: Write Warn) sig m)
  => Type
  -> S.Ann S.Expr
  -> m (Pos Expr)
elabTermDef _T expr@(S.Ann s _ _) = do
  runElabTerm $ pushSpan s $ check (thunk (go (checkExprNeg expr)) ::: _T)
  where
  go k = Check $ \ _T -> case _T of
    ForAll{}                                -> check (tlam (go k) ::: _T)
    Arrow (Just n) q (Thunk (Comp s _A)) _B -> check (lam [(PEff <$> allP n, go k)] ::: Arrow Nothing q (Thunk (Comp s _A)) _B)
    Arrow (Just n) q                _A   _B -> check (lam [(PVal <$> varP n, go k)] ::: Arrow Nothing q _A _B)
    -- FIXME: this doesn’t do what we want for tacit definitions, i.e. where _T is itself a telescope.
    -- FIXME: eta-expanding here doesn’t help either because it doesn’t change the way elaboration of the surface term occurs.
    -- we’ve exhausted the named parameters; the rest is up to the body.
    _                                       -> check (k ::: _T)


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
        _T <- runModule $ runElabType $ check (switch (elabKind ty) ::: Type)
        let (cons, elab) = case k of
              S.DataDef      -> (DData,      elabDataDef)
              S.InterfaceDef -> (DInterface, elabInterfaceDef)
        scope_.decls_.at dname .= Just (cons mempty _T)
        decls <- runModule $ elab (dname ::: _T) cs
        for_ decls $ \ (dname :=: decl) -> scope_.decls_.at dname .= Just decl

      S.TermDef t -> do
        _T <- runModule $ runElabType $ getPos <$> check (switch (elabPosType ty) ::: Type)
        scope_.decls_.at dname .= Just (DTerm Nothing (Pos _T))
        pure (Just (dname, t ::: _T))

    -- then elaborate the terms
    for_ (catMaybes es) $ \ (dname, t ::: _T) -> do
      t' <- runModule $ elabTermDef _T t
      scope_.decls_.ix dname .= DTerm (Just t') (Pos _T)


-- Errors

expectQuantifier :: (HasCallStack, Has (Throw Err) sig m) => String -> Type -> Elab m (Name ::: Type, Type -> Type)
expectQuantifier = expectMatch (\case{ ForAll n t b -> pure (n ::: t, b) ; _ -> Nothing }) "{_} -> _"

-- | Expect a tacit (non-variable-binding) function type.
expectTacitFunction :: (HasCallStack, Has (Throw Err) sig m) => String -> Type -> Elab m ((Quantity, Type), Type)
expectTacitFunction = expectMatch (\case{ Arrow Nothing q t b -> pure ((q, t), b) ; _ -> Nothing }) "_ -> _"

-- | Expect a computation type with effects.
expectRet :: (HasCallStack, Has (Throw Err) sig m) => String -> Type -> Elab m ([Interface Type], Type)
-- FIXME: expectations should be composable so we can expect a thunk and a comp separately
expectRet = expectMatch (\case{ Comp s t -> pure (s, t) ; _ -> Nothing } <=< unThunk) "[_] _"

-- | Expect a value type wrapping a computation.
expectThunk :: (HasCallStack, Has (Throw Err) sig m) => String -> Type -> Elab m Type
expectThunk = expectMatch unThunk "thunk _"


-- Elaboration

runModule :: Has (State Module) sig m => ReaderC Module m a -> m a
runModule m = do
  mod <- get
  runReader mod m

withSpanB :: Algebra sig m => (a -> Bind m b) -> S.Ann a -> Bind m b
withSpanB k (S.Ann s _ a) = mapBind (pushSpan s) (k a)
