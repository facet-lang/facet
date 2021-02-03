{-# LANGUAGE OverloadedStrings #-}
module Facet.Elab.Term
( -- * Term combinators
  global
, var
, tlam
, lam
, thunk
, force
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
) where

import           Control.Algebra
import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Effect.Lens (view, (.=))
import           Control.Effect.Throw
import           Control.Lens (at, ix)
import           Control.Monad (when)
import           Data.Either (fromLeft)
import           Data.Foldable
import           Data.Maybe (catMaybes)
import qualified Data.Set as Set
import           Data.Text (Text)
import           Data.Traversable (for, mapAccumL)
import           Facet.Context (Binding(..))
import           Facet.Core.Module as Module
import           Facet.Core.Term as E hiding (global, var)
import           Facet.Core.Type as T hiding (global, var)
import           Facet.Effect.Write
import           Facet.Elab
import           Facet.Elab.Type
import           Facet.Graph
import           Facet.Name
import           Facet.Semiring (Few(..), zero)
import           Facet.Span (Span(..))
import           Facet.Stack
import qualified Facet.Surface as S
import           Facet.Syntax
import           GHC.Stack

-- Term combinators

-- FIXME: we’re instantiating when inspecting types in the REPL.
global :: Algebra sig m => Q Name ::: Type -> Synth m Expr
global (q ::: _T) = Synth $ instantiate XInst (XVar (Global q) ::: _T)

-- FIXME: do we need to instantiate here to deal with rank-n applications?
-- FIXME: effect ops not in the sig are reported as not in scope
-- FIXME: effect ops in the sig are available whether or not they’re in scope
var :: (HasCallStack, Has (Throw Err) sig m) => Q Name -> Synth m Expr
var n = Synth $ ask >>= \ ElabContext{ module', graph, context, sig } -> if
  | Just (i, _T)    <- lookupInContext n context       -> pure (XVar (Free i) ::: _T)
  | Just (n ::: _T) <- lookupInSig n module' graph sig -> instantiate XInst (XOp n ::: _T)
  | otherwise                                          -> do
    n :=: _ ::: _T <- resolveQ n
    synth $ global (n ::: _T)


tlam :: (HasCallStack, Has (Throw Err) sig m) => Check m Expr -> Check m Expr
tlam b = Check $ \ _T -> do
  (n ::: _A, _B) <- expectQuantifier "when checking type abstraction" _T
  d <- depth
  b' <- Binding n zero _A |- check (b ::: _B (T.free d))
  pure $ XTLam b'

lam :: (HasCallStack, Has (Throw Err) sig m) => [(Bind m (Pattern Name), Check m Expr)] -> Check m Expr
lam cs = Check $ \ _T -> do
  (_A, _B) <- expectTacitFunction "when checking clause" _T
  XLam <$> traverse (\ (p, b) -> check (bind (p ::: _A) b ::: _B)) cs


thunk :: Algebra sig m => Check m a -> Check m a
thunk e = Check $ \case
  VTComp s t -> extendSig s $ check (e ::: t)
  t          -> check (e ::: t)

force :: (HasCallStack, Has (Throw Err) sig m) => Synth m a -> Synth m a
force e = Synth $ do
  e' ::: _T <- synth e
  -- FIXME: should we check the signature? or can we rely on it already having been checked?
  (_s, _T') <- expectComp "when forcing computation" _T
  pure $ e' ::: _T'


string :: Text -> Synth m Expr
string s = Synth $ pure $ XString s ::: VTString


-- Pattern combinators

wildcardP :: Bind m (ValuePattern Name)
wildcardP = Bind $ \ _ _ -> fmap (PWildcard,)

varP :: Algebra sig m => Name -> Bind m (ValuePattern Name)
varP n = Bind $ \ _sig _A b -> Check $ \ _B -> (PVar n,) <$> (Binding n Many _A |- check (b ::: _B))

conP :: (HasCallStack, Has (Throw Err) sig m) => Q Name -> [Bind m (ValuePattern Name)] -> Bind m (ValuePattern Name)
conP n ps = Bind $ \ sig _A b -> Check $ \ _B -> do
  q :=: _ ::: _T <- resolveC n
  _ ::: _T' <- instantiate const (() ::: _T)
  (ps', b') <- check (bind (fieldsP (Bind (\ _sig _A' b -> ([],) <$> Check (\ _B -> unify _A' _A *> check (b ::: _B)))) ps ::: (sig, _T')) b ::: _B)
  pure (PCon q (fromList ps'), b')

fieldsP :: (HasCallStack, Has (Throw Err) sig m) => Bind m [a] -> [Bind m a] -> Bind m [a]
fieldsP = foldr cons
  where
  cons p ps = Bind $ \ sig _A b -> Check $ \ _B -> do
    -- FIXME: assert that the signature is empty
    (_ ::: _A', _A'') <- expectFunction "when checking nested pattern" _A
    (p', (ps', b')) <- check (bind (p ::: (sig, _A')) (bind (ps ::: (sig, _A'')) b) ::: _B)
    pure (p':ps', b')


allP :: Has (Write Warn) sig m => Name -> Bind m (Pattern Name)
allP n = Bind $ \ sig _A b -> Check $ \ _B -> do
  when (null sig) (warn (RedundantCatchAll n))
  Binding n Many _A |- (PAll n,) <$> check (b ::: _B)

effP :: (HasCallStack, Has (Throw Err) sig m) => Q Name -> [Bind m (ValuePattern Name)] -> Name -> Bind m (Pattern Name)
effP n ps v = Bind $ \ sig _A b -> Check $ \ _B -> do
  ElabContext{ module', graph } <- ask
  q ::: _T <- maybe (freeVariable n) (instantiate const) (lookupInSig n module' graph sig)
  (ps', b') <- check (bind (fieldsP (Bind (\ _sig _A' b -> ([],) <$> Check (\ _B -> Binding v Many (VTArrow (Right []) _A' _A) |- check (b ::: _B)))) ps ::: (sig, _T)) b ::: _B)
  pure (PEff q (PVal <$> fromList ps') v, b')


-- Expression elaboration

synthExpr :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> Synth m Expr
synthExpr (S.Ann s _ e) = mapSynth (setSpan s) $ case e of
  S.Var n    -> var n
  S.App f a  -> app XApp (synthExpr f) (checkExpr a)
  S.As t _T  -> as (checkExpr t ::: checkType _T)
  S.String s -> string s
  S.Hole{}   -> nope
  S.Lam{}    -> nope
  S.Thunk{}  -> nope
  S.Force e  -> force (synthExpr e)
  where
  nope = Synth $ couldNotSynthesize (show e)

checkExpr :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.Expr -> Check m Expr
checkExpr expr@(S.Ann s _ e) = mapCheck (setSpan s) $ case e of
  S.Hole  n  -> hole n
  S.Lam cs   -> lam (map (\ (S.Clause p b) -> (bindPattern p, checkExpr b)) cs)
  S.Thunk e  -> thunk (checkExpr e)
  S.Force{}  -> synth
  S.Var{}    -> synth
  S.App{}    -> synth
  S.As{}     -> synth
  S.String{} -> synth
  where
  synth = switch (synthExpr expr)


-- FIXME: check for unique variable names
bindPattern :: (HasCallStack, Has (Throw Err :+: Write Warn) sig m) => S.Ann S.EffPattern -> Bind m (Pattern Name)
bindPattern = go where
  go = withSpanB $ \case
    S.PAll n      -> allP n
    S.PVal p      -> PVal <$> goVal p
    S.PEff n ps v -> effP n (map goVal ps) v

  goVal = withSpanB $ \case
    S.PWildcard -> wildcardP
    S.PVar n    -> varP n
    S.PCon n ps -> conP n (map goVal ps)


-- | Elaborate a type abstracted over another type’s parameters.
--
-- This is used to elaborate data constructors & effect operations, which receive the type/interface parameters as implicit parameters ahead of their own explicit ones.
abstract :: Algebra sig m => Elab m TExpr -> Type -> Elab m TExpr
abstract body = go
  where
  go = \case
    VTForAll       n  t b -> do
      level <- depth
      b' <- Binding n zero t |- go (b (T.free level))
      pure $ TForAll n (T.quote level t) b'
    VTArrow  (Left n) a b -> do
      level <- depth
      b' <- Binding n zero a |- go b
      pure $ TForAll n (T.quote level a) b'
    _                     -> body


-- Declarations

elabDataDef
  :: Has (Reader Graph :+: Reader Module :+: Throw Err) sig m
  => Name ::: Type
  -> [S.Ann (Name ::: S.Ann S.Type)]
  -> m [Name :=: Maybe Def ::: Type]
-- FIXME: check that all constructors return the datatype.
elabDataDef (dname ::: _T) constructors = do
  mname <- view name_
  cs <- for constructors $ runWithSpan $ \ (n ::: t) -> do
    c_T <- elabType $ abstract (check (checkType t ::: VKType)) _T
    con' <- elabTerm $ check (con (mname :.: n) ::: c_T)
    pure $ n :=: Just (DTerm con') ::: c_T
  pure
    $ (dname :=: Just (DData (scopeFromList cs)) ::: _T)
    : cs
  where
  con q = go Nil Nil where
    go ts fs = Check $ \case
      -- FIXME: earlier indices should be shifted
      -- FIXME: XTLam is only for the type parameters
      -- type parameters presumably shouldn’t be represented in the elaborated data
      VTForAll n _T _B -> do
        d <- depth
        check (tlam (go (ts :> d) fs) ::: VTForAll n _T _B)
      VTArrow  n _A _B -> do
        d <- depth
        check (lam [(PVal <$> varP (fromLeft __ n), go ts (fs :> d))] ::: VTArrow n _A _B)
      _T               -> do
        d <- depth
        pure $ XCon q (TVar . TFree . levelToIndex d <$> ts) (XVar . Free . levelToIndex d <$> fs)

elabInterfaceDef
  :: Has (Reader Graph :+: Reader Module :+: Throw Err) sig m
  => Type
  -> [S.Ann (Name ::: S.Ann S.Type)]
  -> m (Maybe Def ::: Type)
elabInterfaceDef _T constructors = do
  cs <- for constructors $ runWithSpan $ \ (n ::: t) -> do
    _T' <- elabType $ abstract (check (checkType t ::: VKType)) _T
    -- FIXME: check that the interface is a member of the sig.
    pure $ n :=: Nothing ::: _T'
  pure $ Just (DInterface (scopeFromList cs)) ::: _T

-- FIXME: add a parameter for the effect signature.
elabTermDef
  :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Throw Err :+: Write Warn) sig m)
  => Type
  -> S.Ann S.Expr
  -> m Value
elabTermDef _T expr = runReader (S.ann expr) $ do
  elabTerm $ check (go (checkExpr expr) ::: _T)
  where
  go k = Check $ \ _T -> case _T of
    VTForAll{}             -> check (tlam (go k) ::: _T)
    VTArrow (Left n) _A _B -> check (lam [(PVal <$> varP n, go k)] ::: VTArrow (Right []) _A _B)
    -- FIXME: this doesn’t do what we want for tacit definitions, i.e. where _T is itself a telescope.
    -- FIXME: eta-expanding here doesn’t help either because it doesn’t change the way elaboration of the surface term occurs.
    -- we’ve exhausted the named parameters; the rest is up to the body.
    _                      -> check (k ::: _T)


-- Modules

elabModule
  :: (HasCallStack, Has (Reader Graph :+: Throw Err :+: Write Warn) sig m)
  => S.Ann S.Module
  -> m Module
elabModule (S.Ann s _ (S.Module mname is os ds)) = execState (Module mname [] os mempty) . runReader s $ do
  let (importedNames, imports) = mapAccumL (\ names (S.Ann _ _ S.Import{ name }) -> (Set.insert name names, Import name)) Set.empty is
  imports_ .= imports

  local (`restrict` importedNames) $ do
    -- FIXME: maybe figure out the graph for mutual recursion?
    -- FIXME: check for redundant naming

    -- elaborate all the types first
    es <- for ds $ \ (S.Ann _ _ (dname, S.Ann s _ (S.Decl tele def))) -> local (const s) $ do
      _T <- runModule $ elabType $ check (checkType tele ::: VKType)

      scope_.decls_.at dname .= Just (Nothing ::: _T)
      case def of
        S.DataDef cs -> Nothing <$ do
          decls <- runModule $ elabDataDef (dname ::: _T) cs
          for_ decls $ \ (dname :=: decl) -> scope_.decls_.at dname .= Just decl

        S.InterfaceDef os -> Nothing <$ do
          decl <- runModule $ elabInterfaceDef _T os
          scope_.decls_.at dname .= Just decl

        S.TermDef t -> pure (Just (S.ann tele, dname, t ::: _T))

    -- then elaborate the terms
    for_ (catMaybes es) $ \ (s, dname, t ::: _T) -> local (const s) $ do
      t' <- runModule $ elabTermDef _T t
      scope_.decls_.ix dname .= (Just (DTerm t') ::: _T)


-- Errors

expectQuantifier :: (HasCallStack, Has (Throw Err) sig m) => String -> Type -> Elab m (Name ::: Type, Type -> Type)
expectQuantifier = expectMatch (\case{ VTForAll n t b -> pure (n ::: t, b) ; _ -> Nothing }) "{_} -> _"

-- | Expect a tacit (non-variable-binding) function type.
expectTacitFunction :: (HasCallStack, Has (Throw Err) sig m) => String -> Type -> Elab m (([Type], Type), Type)
expectTacitFunction = expectMatch (\case{ VTArrow (Right s) t b -> pure ((s, t), b) ; _ -> Nothing }) "_ -> _"

expectComp :: (HasCallStack, Has (Throw Err) sig m) => String -> Type -> Elab m ([Type], Type)
expectComp = expectMatch (\case { VTComp s t -> pure (s, t) ; _ -> Nothing }) "{_}"


-- Elaboration

runModule :: Has (State Module) sig m => ReaderC Module m a -> m a
runModule m = do
  mod <- get
  runReader mod m

runWithSpan :: (a -> ReaderC Span m b) -> S.Ann a -> m b
runWithSpan k (S.Ann s _ a) = runReader s (k a)

withSpanB :: Algebra sig m => (a -> Bind m b) -> S.Ann a -> Bind m b
withSpanB k (S.Ann s _ a) = mapBind (setSpan s) (k a)
