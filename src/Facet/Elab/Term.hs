{-# LANGUAGE OverloadedStrings #-}
module Facet.Elab.Term
( -- * General combinators
  switch
, as
  -- * Term combinators
, global
, var
, tlam
, lam
, app
, string
  -- * Pattern combinators
, wildcardP
, varP
, conP
, fieldsP
, allP
, effP
  -- * Expression elaboration
, synthExpr
, checkExpr
, bindPattern
  -- * Declarations
, elabDataDef
, elabInterfaceDef
, elabTermDef
  -- * Modules
, elabModule
  -- * Elaboration
, require
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
import           Control.Effect.Writer (censor)
import           Control.Lens (at, ix)
import           Control.Monad ((<=<))
import           Data.Bifunctor (first)
import           Data.Foldable
import           Data.Functor
import           Data.Maybe (catMaybes, fromMaybe, listToMaybe)
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
import           Facet.Lens (locally)
import           Facet.Name
import           Facet.Semiring (Few(..), zero, (><<))
import           Facet.Snoc
import           Facet.Snoc.NonEmpty as NE
import           Facet.Source (Source)
import qualified Facet.Surface as S
import           Facet.Syntax
import           Facet.Usage hiding (restrict)
import           GHC.Stack

-- General combinators

switch :: (HasCallStack, Has (Throw Err) sig m) => Synth m a -> Check m a
switch (Synth m) = Check $ \ _T -> m >>= \case
  a ::: VComp req _T' -> require req >> unify _T' _T $> a
  a :::           _T' -> unify _T' _T $> a

as :: (HasCallStack, Has (Throw Err) sig m) => Check m Expr ::: IsType m TExpr -> Synth m Expr
as (m ::: _T) = Synth $ do
  env <- views context_ toEnv
  subst <- get
  _T' <- T.eval subst (Left <$> env) <$> checkIsType (_T ::: KType)
  a <- check (m ::: _T')
  pure $ a ::: _T'


-- Term combinators

-- FIXME: we’re instantiating when inspecting types in the REPL.
global :: Algebra sig m => RName ::: Type -> Synth m Expr
global (q ::: _T) = Synth $ instantiate XInst (XVar (Global q) ::: _T)

-- FIXME: do we need to instantiate here to deal with rank-n applications?
-- FIXME: effect ops not in the sig are reported as not in scope
-- FIXME: effect ops in the sig are available whether or not they’re in scope
var :: (HasCallStack, Has (Throw Err) sig m) => QName -> Synth m Expr
var n = Synth $ ask >>= \ StaticContext{ module', graph } -> ask >>= \ ElabContext{ context, sig } -> if
  | [(i, q, Right _T)] <- lookupInContext n context              -> use i q $> (XVar (Free i) ::: _T)
  | [_ :=: DTerm (Just x) _T] <- lookupInSig n module' graph sig -> instantiate XInst (x ::: _T)
  | otherwise                                                    -> resolveQ n >>= \case
    n :=: DTerm _ _T -> synth $ global (n ::: _T)
    _ :=: _          -> freeVariable n


hole :: (HasCallStack, Has (Throw Err) sig m) => Name -> Check m a
hole n = Check $ \ _T -> withFrozenCallStack $ err $ Hole n _T


tlam :: (HasCallStack, Has (Throw Err) sig m) => Check m Expr -> Check m Expr
tlam b = Check $ \ _T -> do
  (n ::: _A, _B) <- assertQuantifier _T
  d <- depth
  b' <- Binding n zero (Left _A) |- check (b ::: _B (T.free d))
  pure $ XTLam b'

lam :: (HasCallStack, Has (Throw Err) sig m) => [(Bind m (Pattern Name), Check m Expr)] -> Check m Expr
lam cs = Check $ \ _T -> do
  (_A, _B) <- assertTacitFunction _T
  XLam <$> traverse (\ (p, b) -> check (bind (p ::: _A) b ::: _B)) cs

app :: (HasCallStack, Has (Throw Err) sig m) => (a -> b -> c) -> Synth m a -> Check m b -> Synth m c
app mk f a = Synth $ do
  f' ::: _F <- synth f
  (_ ::: (q, _A), _B) <- assertFunction _F
  a' <- censor @Usage (q ><<) $ check (a ::: _A)
  pure $ mk f' a' ::: _B


string :: Text -> Synth m Expr
string s = Synth $ pure $ XString s ::: T.VString


-- Pattern combinators

wildcardP :: Bind m (ValuePattern Name)
wildcardP = Bind $ \ _ _ -> fmap (PWildcard,)

varP :: (HasCallStack, Has (Throw Err) sig m) => Name -> Bind m (ValuePattern Name)
varP n = Bind $ \ q _A b -> Check $ \ _B -> (PVar n,) <$> (Binding n q (Right (wrap _A)) |- check (b ::: _B))
  where
  wrap = \case
    VComp sig _A -> VArrow Nothing Many (VNe (Global (NE.FromList ["Data", "Unit"] :.: U "Unit")) Nil) (VComp sig _A)
    _T           -> _T

conP :: (HasCallStack, Has (Throw Err) sig m) => QName -> [Bind m (ValuePattern Name)] -> Bind m (ValuePattern Name)
conP n ps = Bind $ \ q _A b -> Check $ \ _B -> do
  n' :=: _ ::: _T <- resolveC n
  _ ::: _T' <- instantiate const (() ::: _T)
  (ps', b') <- check (bind (fieldsP (Bind (\ _q' _A' b -> ([],) <$> Check (\ _B -> unify _A' _A *> check (b ::: _B)))) ps ::: (q, _T')) b ::: _B)
  pure (PCon n' (fromList ps'), b')

fieldsP :: (HasCallStack, Has (Throw Err) sig m) => Bind m [a] -> [Bind m a] -> Bind m [a]
fieldsP = foldr cons
  where
  cons p ps = Bind $ \ q _A b -> Check $ \ _B -> do
    (_ ::: (q', _A'), _A'') <- assertFunction _A
    (p', (ps', b')) <- check (bind (p ::: (q', _A')) (bind (ps ::: (q, _A'')) b) ::: _B)
    pure (p':ps', b')


allP :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => Name -> Bind m (EffectPattern Name)
allP n = Bind $ \ q _A b -> Check $ \ _B -> do
  (sig, _T) <- assertComp _A
  (PAll n,) <$> (Binding n q (Right (VArrow Nothing Many (VNe (Global (NE.FromList ["Data", "Unit"] :.: U "Unit"))  Nil) (VComp sig _T))) |- check (b ::: _B))

effP :: (HasCallStack, Has (Throw Err) sig m) => QName -> [Bind m (ValuePattern Name)] -> Name -> Bind m (Pattern Name)
effP n ps v = Bind $ \ q _A b -> Check $ \ _B -> do
  StaticContext{ module', graph } <- ask
  (sig, _A') <- assertComp _A
  n' ::: _T <- maybe (freeVariable n) (\ (n :=: _ ::: _T) -> instantiate const (n ::: _T)) (listToMaybe (traverse unDTerm =<< lookupInSig n module' graph sig))
  (ps', b') <- check (bind (fieldsP (Bind (\ q' _A' b -> ([],) <$> Check (\ _B -> Binding v q' (Right (VArrow Nothing Many _A' _A)) |- check (b ::: _B)))) ps ::: (q, _T)) b ::: _B)
  pure (peff n' (fromList ps') v, b')


-- Expression elaboration

synthExpr :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> Synth m Expr
synthExpr (S.Ann s _ e) = mapSynth (pushSpan s) $ case e of
  S.Var n    -> var n
  S.App f a  -> app XApp (synthExpr f) (checkExpr a)
  S.As t _T  -> as (checkExpr t ::: synthType _T)
  S.String s -> string s
  S.Hole{}   -> nope
  S.Lam{}    -> nope
  where
  nope = Synth couldNotSynthesize

checkExpr :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> Check m Expr
checkExpr expr@(S.Ann s _ e) = mapCheck (pushSpan s) $ case e of
  S.Hole  n  -> hole n
  S.Lam cs   -> lam (map (\ (S.Clause p b) -> (bindPattern p, checkExpr b)) cs)
  S.Var{}    -> synth
  S.App{}    -> synth
  S.As{}     -> synth
  S.String{} -> synth
  where
  synth = switch (synthExpr expr)


-- FIXME: check for unique variable names
bindPattern :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Pattern -> Bind m (Pattern Name)
bindPattern = go where
  go = withSpanB $ \case
    S.PVal p -> Bind $ \ q _T -> bind (PVal <$> goVal p ::: (q, maybe _T snd (unComp _T)))
    S.PEff p -> withSpanB (\ (S.POp n ps v) -> effP n (map goVal ps) v) p

  goVal = withSpanB $ \case
    S.PWildcard -> wildcardP
    S.PVar n    -> varP n
    S.PCon n ps -> conP n (map goVal ps)


-- | Elaborate a type abstracted over another type’s parameters.
--
-- This is used to elaborate data constructors & effect operations, which receive the type/interface parameters as implicit parameters ahead of their own explicit ones.
abstractType :: (HasCallStack, Has (Throw Err) sig m) => Elab m TExpr -> Kind -> Elab m TExpr
abstractType body = go
  where
  go = \case
    KArrow  (Just n) a b -> TForAll n a <$> (Binding n zero (Left a) |- go b)
    _                    -> body

abstractTerm :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => (Snoc TExpr -> Snoc Expr -> Expr) -> Check m Expr
abstractTerm body = go Nil Nil
  where
  go ts fs = Check $ \case
    VForAll n   _T _B -> do
      d <- depth
      check (tlam (go (ts :> d) fs) ::: VForAll n _T _B)
    VArrow  n q _A _B -> do
      d <- depth
      check (lam [(patternForArgType _A (fromMaybe __ n), go ts (fs :> \ d' -> XVar (Free (levelToIndex d' d))))] ::: VArrow n q _A _B)
    _T                 -> do
      d <- depth
      pure $ body (TVar . Free . Right . levelToIndex d <$> ts) (fs <*> pure d)

patternForArgType :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => Type -> Name -> Bind m (Pattern Name)
patternForArgType = \case
  VComp{} -> fmap PEff . allP
  _       -> fmap PVal . varP


-- Declarations

elabDataDef
  :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source :+: Throw Err :+: Write Warn) sig m)
  => Name ::: Kind
  -> [S.Ann (Name ::: S.Ann S.Type)]
  -> m [Name :=: Def]
-- FIXME: check that all constructors return the datatype.
elabDataDef (dname ::: _K) constructors = do
  mname <- view name_
  cs <- for constructors $ \ (S.Ann _ _ (n ::: t)) -> do
    c_T <- elabType $ abstractType (checkIsType (synthType t ::: KType)) _K
    con' <- elabTerm $ check (abstractTerm (XCon (mname :.: n)) ::: c_T)
    pure $ n :=: DTerm (Just con') c_T
  pure
    $ (dname :=: DData (scopeFromList cs) _K)
    : cs

elabInterfaceDef
  :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source :+: Throw Err :+: Write Warn) sig m)
  => Name ::: Kind
  -> [S.Ann (Name ::: S.Ann S.Type)]
  -> m [Name :=: Def]
elabInterfaceDef (dname ::: _T) constructors = do
  mname <- view name_
  cs <- for constructors $ \ (S.Ann _ _ (n ::: t)) -> do
    _T' <- elabType $ abstractType (checkIsType (synthType t ::: KType)) _T
    -- FIXME: check that the interface is a member of the sig.
    op' <- elabTerm $ check (abstractTerm (XOp (mname :.: n)) ::: _T')
    pure $ n :=: DTerm (Just op') _T'
  pure [ dname :=: DInterface (scopeFromList cs) _T ]

-- FIXME: add a parameter for the effect signature.
elabTermDef
  :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source :+: Throw Err :+: Write Warn) sig m)
  => Type
  -> S.Ann S.Expr
  -> m Expr
elabTermDef _T expr@(S.Ann s _ _) = do
  elabTerm $ pushSpan s $ check (go (checkExpr expr) ::: _T)
  where
  go k = Check $ \ _T -> case _T of
    VForAll{}               -> check (tlam (go k) ::: _T)
    VArrow (Just n) q _A _B -> check (lam [(PVal <$> varP n, go k)] ::: VArrow Nothing q _A _B)
    -- FIXME: this doesn’t do what we want for tacit definitions, i.e. where _T is itself a telescope.
    -- FIXME: eta-expanding here doesn’t help either because it doesn’t change the way elaboration of the surface term occurs.
    -- we’ve exhausted the named parameters; the rest is up to the body.
    _                       -> check (k ::: _T)


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
    es <- for ds $ \ (S.Ann _ _ (dname, S.Ann _ _ def)) -> case def of
      S.DataDef cs tele -> Nothing <$ do
        _K <- runModule $ elabKind $ checkIsType (synthKind tele ::: KType)
        scope_.decls_.at dname .= Just (DData mempty _K)
        decls <- runModule $ elabDataDef (dname ::: _K) cs
        for_ decls $ \ (dname :=: decl) -> scope_.decls_.at dname .= Just decl

      S.InterfaceDef os tele -> Nothing <$ do
        _K <- runModule $ elabKind $ checkIsType (synthKind tele ::: KType)
        scope_.decls_.at dname .= Just (DInterface mempty _K)
        decls <- runModule $ elabInterfaceDef (dname ::: _K) os
        for_ decls $ \ (dname :=: decl) -> scope_.decls_.at dname .= Just decl

      S.TermDef t tele -> do
        _T <- runModule $ elabType $ checkIsType (synthType tele ::: KType)
        scope_.decls_.at dname .= Just (DTerm Nothing _T)
        pure (Just (dname, t ::: _T))

    -- then elaborate the terms
    for_ (catMaybes es) $ \ (dname, t ::: _T) -> do
      t' <- runModule $ elabTermDef _T t
      scope_.decls_.ix dname .= DTerm (Just t') _T


-- Errors

assertQuantifier :: (HasCallStack, Has (Throw Err) sig m) => Type -> Elab m (Name ::: Kind, Type -> Type)
assertQuantifier = assertMatch (\case{ Right (VForAll n t b) -> pure (n ::: t, b) ; _ -> Nothing }) "{_} -> _" . Right

-- | Expect a tacit (non-variable-binding) function type.
assertTacitFunction :: (HasCallStack, Has (Throw Err) sig m) => Type -> Elab m ((Quantity, Type), Type)
assertTacitFunction = assertMatch (\case{ Right (VArrow Nothing q t b) -> pure ((q, t), b) ; _ -> Nothing }) "_ -> _" . Right

-- | Expect a computation type with effects.
assertComp :: (HasCallStack, Has (Throw Err) sig m) => Type -> Elab m ([Type], Type)
assertComp = assertMatch (unComp <=< either (const Nothing) Just) "[_] _" . Right


-- Elaboration

runModule :: Has (State Module) sig m => ReaderC Module m a -> m a
runModule m = do
  mod <- get
  runReader mod m

withSpanB :: Algebra sig m => (a -> Bind m b) -> S.Ann a -> Bind m b
withSpanB k (S.Ann s _ a) = mapBind (pushSpan s) (k a)

provide :: Has (Reader ElabContext) sig m => [Type] -> m a -> m a
provide = locally sig_ . (++)

require :: [Type] -> Elab m ()
require _ = pure () -- FIXME: validate the requirements against the provided sig


-- Judgements

check :: Algebra sig m => (Check m a ::: Type) -> Elab m a
check (m ::: _T) = case _T of
  VComp sig _T -> provide sig $ runCheck m _T
  _T           -> runCheck m _T

newtype Check m a = Check { runCheck :: Type -> Elab m a }
  deriving (Applicative, Functor) via ReaderC Type (Elab m)

mapCheck :: (Elab m a -> Elab m b) -> Check m a -> Check m b
mapCheck f m = Check $ \ _T -> f (runCheck m _T)


newtype Synth m a = Synth { synth :: Elab m (a ::: Type) }

instance Functor (Synth m) where
  fmap f (Synth m) = Synth (first f <$> m)

mapSynth :: (Elab m (a ::: Type) -> Elab m (b ::: Type)) -> Synth m a -> Synth m b
mapSynth f = Synth . f . synth


bind :: Bind m a ::: (Quantity, Type) -> Check m b -> Check m (a, b)
bind (p ::: (q, _T)) = runBind p q _T

newtype Bind m a = Bind { runBind :: forall x . Quantity -> Type -> Check m x -> Check m (a, x) }
  deriving (Functor)

mapBind :: (forall x . Elab m (a, x) -> Elab m (b, x)) -> Bind m a -> Bind m b
mapBind f m = Bind $ \ q _A b -> mapCheck f (runBind m q _A b)
