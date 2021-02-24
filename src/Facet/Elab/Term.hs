{-# LANGUAGE GADTs #-}
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
  -- * Pattern combinators
, wildcardP
, varP
, conP
, fieldsP
, allP
, effP
  -- * Expression elaboration
, synthExprN
, checkExprN
, synthExprP
, checkExprP
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
import           Control.Lens (at, ix)
import           Control.Monad ((<=<))
import           Data.Foldable
import           Data.Functor
import           Data.Maybe (catMaybes, fromMaybe)
import qualified Data.Set as Set
import           Data.Text (Text)
import           Data.Traversable (for, mapAccumL)
import           Facet.Context (Binding(..), VarType(..))
import           Facet.Core.Module as Module
import           Facet.Core.Term as E
import           Facet.Core.Type as T hiding (global)
import           Facet.Effect.Write
import           Facet.Elab
import           Facet.Elab.Type
import           Facet.Graph
import           Facet.Name
import           Facet.Semiring (Few(..), zero)
import           Facet.Snoc
import           Facet.Source (Source)
import qualified Facet.Surface as S
import           Facet.Syntax
import           Facet.Usage hiding (restrict)
import           GHC.Stack

-- Term combinators

-- FIXME: how the hell are we supposed to handle instantiation?
global :: Q Name ::: Type P -> Synth P m (Expr P)
global (q ::: _T) = Synth $ pure $ XVar (Global q) ::: _T

-- FIXME: do we need to instantiate here to deal with rank-n applications?
-- FIXME: effect ops not in the sig are reported as not in scope
-- FIXME: effect ops in the sig are available whether or not they’re in scope
var :: (HasCallStack, Has (Throw Err) sig m) => Q Name -> Synth P m (Expr P)
var n = Synth $ ask >>= \ StaticContext{ module', graph } -> ask >>= \ ElabContext{ context, sig } -> if
  | Just (i, q, Tm _T) <- lookupInContext n context       -> use i q $> (XVar (Free i) ::: _T)
  | Just (_ :=: DTerm (Just x) _T) <- lookupInSig n module' graph sig -> pure (x ::: _T)
  | otherwise                                             -> do
    n :=: d <- resolveQ n
    _T <- case d of
      DTerm _ _T -> pure _T
      _          -> freeVariable n
    synth $ global (n ::: _T)


tlam :: (HasCallStack, Has (Throw Err) sig m) => Check N m (Expr N) -> Check N m (Expr N)
tlam b = Check $ \ _T -> do
  (n ::: _A, _B) <- expectQuantifier "when checking type abstraction" _T
  d <- depth
  b' <- Binding n zero (Ty _A) |- check (b ::: _B (free d))
  pure $ XTLam b'

lam :: (HasCallStack, Has (Throw Err) sig m) => [(Bind P N m (Pattern Name), Check N m (Expr N))] -> Check N m (Expr N)
lam cs = Check $ \ _T -> do
  (_A, _B) <- expectTacitFunction "when checking clause" _T
  XLam <$> traverse (\ (p, b) -> check (bind (p ::: _A) b ::: _B)) cs


string :: Text -> Synth P m (Expr P)
string s = Synth $ pure $ XString s ::: T.String


-- Polarity shifts

force :: Has (Throw Err) sig m => Check P m (Expr P) -> Check N m (Expr N)
force t = Check $ \ _T -> XForce <$> check (t ::: Thunk _T)

thunk :: (HasCallStack, Has (Throw Err) sig m) => Check N m (Expr N) -> Check P m (Expr P)
thunk c = Check $ \ _T -> do
  _C <- expectThunk "when thunking computation" _T
  c' <- check (c ::: _C)
  pure $ XThunk c'

thunkS :: Synth N m (Expr N) -> Synth P m (Expr P)
thunkS c = Synth $ do
  c' ::: _C <- synth c
  pure $ XThunk c' ::: Thunk _C

retS :: Synth P m (Expr P) -> Synth N m (Expr N)
retS v = Synth $ do
  v' ::: _V <- synth v
  pure $ XReturn v' ::: Comp [] _V


-- Pattern combinators

wildcardP :: Bind P N m (ValuePattern Name)
wildcardP = Bind $ \ _ _ -> fmap (PWildcard,)

varP :: (HasCallStack, Has (Throw Err) sig m) => Name -> Bind P N m (ValuePattern Name)
varP n = Bind $ \ q _A b -> Check $ \ _B -> (PVar n,) <$> (Binding n q (Tm _A) |- check (b ::: _B))

conP :: (HasCallStack, Has (Throw Err) sig m) => Q Name -> [Bind P N m (ValuePattern Name)] -> Bind P N m (ValuePattern Name)
conP n ps = Bind $ \ q _A b -> Check $ \ _B -> do
  n' :=: _ ::: _T <- traverse (instantiate const) =<< resolveC n
  (ps', b') <- check (bind (fieldsP (Bind (\ _q' _A' b -> ([],) <$> Check (\ _B -> unify _A' _A *> check (b ::: _B)))) ps ::: (q, _T)) b ::: _B)
  pure (PCon n' (fromList ps'), b')

fieldsP :: (HasCallStack, Has (Throw Err) sig m) => Bind P N m [a] -> [Bind P N m a] -> Bind P N m [a]
fieldsP = foldr cons
  where
  cons p ps = Bind $ \ q _A b -> Check $ \ _B -> do
    _A <- expectThunk "when checking nested pattern" _A
    (_ ::: (q', _A'), _A'') <- expectFunction "when checking nested pattern" _A
    (p', (ps', b')) <- check (bind (p ::: (q', _A')) (bind (ps ::: (q, Thunk _A'')) b) ::: _B)
    pure (p':ps', b')


allP :: (HasCallStack, Has (Throw Err) sig m) => Name -> Bind P N m (EffectPattern Name)
allP n = Bind $ \ q _A b -> Check $ \ _B -> do
  (sig, _A') <- expectRet "when checking catch-all pattern" _A
  (PAll n,) <$> (Binding n q (Tm (Thunk (Comp sig _A'))) |- check (b ::: _B))

effP :: (HasCallStack, Has (Throw Err) sig m) => Q Name -> [Bind P N m (ValuePattern Name)] -> Name -> Bind P N m (Pattern Name)
effP n ps v = Bind $ \ q _A b -> Check $ \ _B -> do
  StaticContext{ module', graph } <- ask
  (sig, _A') <- expectRet "when checking effect pattern" _A
  n' ::: _T <- maybe (freeVariable n) (\ (n :=: _ ::: _T) -> instantiate const (n ::: _T)) ((\ (n :=: d) -> (n :=:) <$> unDData d) =<< lookupInSig n module' graph sig)
  (ps', b') <- check (bind (fieldsP (Bind (\ q' _A' b -> ([],) <$> Check (\ _B -> Binding v q' (Tm (Thunk (Arrow Nothing Many _A' (Comp [] _A)))) |- check (b ::: _B)))) ps ::: (q, _T)) b ::: _B)
  pure (peff n' (fromList ps') v, b')


-- Expression elaboration

synthExprN :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> Synth N m (Expr N)
synthExprN expr@(S.Ann s _ e) = mapSynth (pushSpan s) $ case e of
  S.App f a  -> app XApp (synthExprN f) (checkExprP a)
  S.As t _T  -> as (checkExprN t ::: switch (synthTypeN _T))
  S.Var{}    -> shift
  S.String{} -> shift
  S.Hole{}   -> nope
  S.Lam{}    -> nope
  where
  shift = retS (synthExprP expr)
  nope = Synth $ couldNotSynthesize (show e)

checkExprN :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> Check N m (Expr N)
checkExprN expr@(S.Ann s _ e) = mapCheck (pushSpan s) $ case e of
  S.Hole  n  -> hole n
  S.Lam cs   -> lam (map (\ (S.Clause p b) -> (bindPattern p, checkExprN b)) cs)
  S.Var{}    -> synth
  S.App{}    -> synth
  S.As{}     -> synth
  S.String{} -> synth
  where
  synth = switch (synthExprN expr)


synthExprP :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> Synth P m (Expr P)
synthExprP expr@(S.Ann s _ e) = mapSynth (pushSpan s) $ case e of
  S.Var n    -> var n
  S.App{}    -> shift
  S.As t _T  -> as (checkExprP t ::: switch (synthTypeP _T))
  S.String s -> string s
  S.Hole{}   -> nope
  S.Lam{}    -> nope
  where
  shift = thunkS (synthExprN expr)
  nope = Synth $ couldNotSynthesize (show e)

checkExprP :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> Check P m (Expr P)
checkExprP expr@(S.Ann s _ e) = mapCheck (pushSpan s) $ case e of
  S.Hole  n  -> hole n
  S.Lam{}    -> shift
  S.Var{}    -> synth
  S.App{}    -> synth
  S.As{}     -> synth
  S.String{} -> synth
  where
  shift = thunk (checkExprN expr)
  synth = switch (synthExprP expr)


-- FIXME: check for unique variable names
bindPattern :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Pattern -> Bind P N m (Pattern Name)
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
abstractType :: (HasCallStack, Has (Throw Err) sig m) => Elab m (TExpr N) -> Check T m (TExpr N)
abstractType body = go
  where
  go = Check $ \case
    Arrow' (Just n) a b -> do
      level <- depth
      b' <- Binding n zero (Ty a) |- check (go ::: b)
      pure $ TForAll n (T.quote level a) b'
    _                   -> body

abstractTerm :: (HasCallStack, Has (Throw Err) sig m) => (Snoc (TExpr P) -> Snoc (Expr P) -> Expr N) -> Check N m (Expr N)
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
      pure $ body (TVar . Free . levelToIndex d <$> ts) (XVar . Free . levelToIndex d <$> fs)


-- Declarations

elabDataDef
  :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source :+: Throw Err) sig m)
  => Name ::: Type T
  -> [S.Ann (Name ::: S.Ann S.Type)]
  -> m [Name :=: Def]
-- FIXME: check that all constructors return the datatype.
elabDataDef (dname ::: _T) constructors = do
  mname <- view name_
  cs <- for constructors $ \ (S.Ann s _ (n ::: t)) -> do
    c_T <- elabType $ pushSpan s $ TThunk <$> check (abstractType (check (switch (synthTypeN t) ::: Type)) ::: _T)
    con' <- elabTerm $ check (thunk (abstractTerm (\ ts fs -> XReturn (XCon (mname :.: n) ts fs))) ::: c_T)
    pure $ n :=: DTerm (Just con') c_T
  pure
    $ (dname :=: DData (scopeFromList cs) _T)
    : cs

elabInterfaceDef
  :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source :+: Throw Err) sig m)
  => Name ::: Type T
  -> [S.Ann (Name ::: S.Ann S.Type)]
  -> m [Name :=: Def]
elabInterfaceDef (dname ::: _T) constructors = do
  mname <- view name_
  cs <- for constructors $ \ (S.Ann s _ (n ::: t)) -> do
    _T' <- elabType $ pushSpan s $ TThunk <$> check (abstractType (check (switch (synthTypeN t) ::: Type)) ::: _T)
    -- FIXME: check that the interface is a member of the sig.
    op' <- elabTerm $ check (thunk (abstractTerm (XOp (mname :.: n))) ::: _T')
    pure $ n :=: DTerm (Just op') _T'
  pure [ dname :=: DInterface (scopeFromList cs) _T ]

-- FIXME: add a parameter for the effect signature.
elabTermDef
  :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source :+: Throw Err :+: Write Warn) sig m)
  => Type P
  -> S.Ann S.Expr
  -> m (Expr P)
elabTermDef _T expr@(S.Ann s _ _) = do
  elabTerm $ pushSpan s $ check (thunk (go (checkExprN expr)) ::: _T)
  where
  go :: Has (Throw Err) sig m => Check N m (Expr N) -> Check N m (Expr N)
  go k = Check $ \ _T -> case _T of
    ForAll{}                                -> check (tlam (go k) ::: _T)
    Arrow (Just n) q (Thunk (Comp s _A)) _B -> check (lam [(PEff <$> allP n, go k)] ::: Arrow Nothing q (Thunk (Comp s _A)) _B)
    Arrow (Just n) q _A _B                  -> check (lam [(PVal <$> varP n, go k)] ::: Arrow Nothing q _A _B)
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
        _T <- runModule $ elabType $ check (switch (synthTypeT ty) ::: Type)
        let (cons, elab) = case k of
              S.DataDef      -> (DData, elabDataDef)
              S.InterfaceDef -> (DInterface, elabInterfaceDef)
        scope_.decls_.at dname .= Just (cons mempty _T)
        decls <- runModule $ elab (dname ::: _T) cs
        for_ decls $ \ (dname :=: decl) -> scope_.decls_.at dname .= Just decl

      S.TermDef t -> do
        _T <- runModule $ elabType $ check (switch (synthTypeP ty) ::: Type)
        scope_.decls_.at dname .= Just (DTerm Nothing _T)
        pure (Just (dname, t ::: _T))

    -- then elaborate the terms
    for_ (catMaybes es) $ \ (dname, t ::: _T) -> do
      t' <- runModule $ elabTermDef _T t
      scope_.decls_.ix dname .= DTerm (Just t') _T


-- Errors

expectQuantifier :: (HasCallStack, Has (Throw Err) sig m) => String -> Type N -> Elab m (Name ::: Type T, Type P -> Type N)
expectQuantifier = expectMatch (\case{ ForAll n t b -> pure (n ::: t, b) ; _ -> Nothing }) "{_} -> _"

-- | Expect a tacit (non-variable-binding) function type.
expectTacitFunction :: (HasCallStack, Has (Throw Err) sig m) => String -> Type N -> Elab m ((Quantity, Type P), Type N)
expectTacitFunction = expectMatch (\case{ Arrow Nothing q t b -> pure ((q, t), b) ; _ -> Nothing }) "_ -> _"

-- | Expect a computation type with effects.
expectRet :: (HasCallStack, Has (Throw Err) sig m) => String -> Type P -> Elab m ([Type P], Type P)
-- FIXME: expectations should be composable so we can expect a thunk and a comp separately
expectRet = expectMatch (\case{ Comp s t -> pure (s, t) ; _ -> Nothing } <=< unThunk) "[_] _"

-- | Expect a value type wrapping a computation.
expectThunk :: (HasCallStack, Has (Throw Err) sig m) => String -> Type P -> Elab m (Type N)
expectThunk = expectMatch unThunk "thunk _"


-- Elaboration

runModule :: Has (State Module) sig m => ReaderC Module m a -> m a
runModule m = do
  mod <- get
  runReader mod m

withSpanB :: Algebra sig m => (a -> Bind p q m b) -> S.Ann a -> Bind p q m b
withSpanB k (S.Ann s _ a) = mapBind (pushSpan s) (k a)
