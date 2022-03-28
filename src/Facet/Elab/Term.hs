{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
module Facet.Elab.Term
( -- * General combinators
  switch
, as
  -- * Term combinators
, global
, globalS
, var
, varS
, tlam
, lam
, lamS
, app
, appS
, string
, stringS
, let'
, comp
  -- * Pattern combinators
, wildcardP
, varP
, conP
, fieldsP
, allP
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
, bind
, Bind(..)
) where

import           Control.Algebra
import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Carrier.Writer.Church
import           Control.Effect.Throw
import           Data.Bifunctor (first)
import           Data.Either (partitionEithers)
import           Data.Foldable
import           Data.Functor
import           Data.Maybe (catMaybes, fromMaybe, listToMaybe)
import           Data.Monoid (Ap(..), First(..))
import qualified Data.Set as Set
import           Data.Text (Text)
import           Data.Traversable (for, mapAccumL)
import           Facet.Context (level, toEnv)
import           Facet.Effect.Write
import           Facet.Elab
import           Facet.Elab.Type hiding (switch)
import qualified Facet.Elab.Type as Type
import           Facet.Functor.Check
import           Facet.Functor.Compose hiding (Clause)
import           Facet.Functor.Synth
import           Facet.Graph
import           Facet.Interface
import           Facet.Kind
import           Facet.Lens as Lens (locally, view, views, (.=), (<~))
import           Facet.Module as Module
import           Facet.Name
import           Facet.Pattern
import           Facet.Semiring (Few(..), (><<))
import qualified Facet.Sequent.Class as SQ
import           Facet.Snoc
import           Facet.Snoc.NonEmpty as NE
import           Facet.Source (Source)
import           Facet.Subst
import qualified Facet.Surface.Module as S
import qualified Facet.Surface.Term.Expr as S
import qualified Facet.Surface.Type.Expr as S
import           Facet.Syntax as S hiding (context_)
import           Facet.Term.Expr as E
import qualified Facet.Type.Expr as TX
import           Facet.Type.Norm as T hiding (global)
import           Facet.Unify
import           Facet.Usage hiding (restrict)
import           Fresnel.At as At
import           Fresnel.Ixed
import           Fresnel.Prism (Prism')
import           Fresnel.Review (review)
import           Fresnel.Setter (Setter')
import           Fresnel.Traversal (Traversal')
import           GHC.Stack

-- General combinators

switch :: (Has (Reader ElabContext) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason) sig m, Has (Writer Usage) sig m) => m (a :==> Type) -> Type <==: m a
switch m = Check $ \ _Exp -> m >>= \case
  a :==> T.Comp req _Act -> require req >> unify (Exp _Exp) (Act _Act) $> a
  a :==>            _Act -> unify (Exp _Exp) (Act _Act) $> a

as :: (Has (Reader ElabContext) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason) sig m) => (Type <==: m a) ::: m (Type :==> Kind) -> m (a :==> Type)
as (m ::: _T) = do
  _T' <- Type.switch _T <==: KType
  a <- check (m ::: _T')
  pure $ a :==> _T'


-- Term combinators

-- FIXME: we’re instantiating when inspecting types in the REPL.
global :: Has (State (Subst Type)) sig m => RName ::: Type -> m (Term :==> Type)
global (q ::: _T) = (\ (v ::: _T) -> v :==> _T) <$> instantiate const (Var (Global q) ::: _T)

-- FIXME: we’re instantiating when inspecting types in the REPL.
globalS :: (Has (State (Subst Type)) sig m, SQ.Sequent t c d, Applicative i) => RName ::: Type -> m (i t :==> Type)
globalS (q ::: _T) = do
  v <- SQ.varA (Global q)
  (\ (v ::: _T) -> v :==> _T) <$> instantiate const (v ::: _T)

-- FIXME: do we need to instantiate here to deal with rank-n applications?
-- FIXME: effect ops not in the sig are reported as not in scope
-- FIXME: effect ops in the sig are available whether or not they’re in scope
var :: (Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason) sig m, Has (Writer Usage) sig m) => QName -> m (Term :==> Type)
var n = views context_ (lookupInContext n) >>= \case
  [(n', Right (q, _T))] -> use n' q $> (Var (Free n') :==> _T)
  _                     -> resolveQ n >>= \case
    n :=: DTerm _ _T -> global (n ::: _T)
    _ :=: _          -> freeVariable n

-- FIXME: do we need to instantiate here to deal with rank-n applications?
-- FIXME: effect ops not in the sig are reported as not in scope
-- FIXME: effect ops in the sig are available whether or not they’re in scope
varS :: (Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason) sig m, Has (Writer Usage) sig m, SQ.Sequent t c d, Applicative i) => QName -> m (i t :==> Type)
varS n = views context_ (lookupInContext n) >>= \case
  [(n', Right (q, _T))] -> do
    use n' q
    d <- views context_ level
    SQ.varA (Free (toLeveled d (ident n'))) ==> pure _T
  _                     -> resolveQ n >>= \case
    n :=: DTerm _ _T -> globalS (n ::: _T)
    _ :=: _          -> freeVariable n


hole :: Has (Throw ErrReason) sig m => Name -> Type <==: m a
hole n = Check $ \ _T -> withFrozenCallStack $ throwError $ Hole n _T


tlam :: (Has (Reader ElabContext) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason) sig m) => Type <==: m Term -> Type <==: m Term
tlam b = Check $ \ _T -> do
  (n, _A, _B) <- assertQuantifier _T
  d <- depth
  n :==> _A ||- check (b ::: _B (T.free (LName (getUsed d) n)))

lam :: (Has (Reader ElabContext) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason) sig m, Has (Writer Usage) sig m) => [(Bind m (Pattern (Name :==> Type)), Type <==: m Term)] -> Type <==: m Term
lam cs = Check $ \ _T -> do
  (_, q, _A, _B) <- assertTacitFunction _T
  Lam <$> traverse (\ (p, b) -> bind (p ::: (q, _A)) (check (b ::: _B))) cs

lam1 :: (Has (Reader ElabContext) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason) sig m, Has (Writer Usage) sig m) => Bind m (Pattern (Name :==> Type)) -> Type <==: m Term -> Type <==: m Term
lam1 p b = lam [(p, b)]

lamS :: (Has (Reader ElabContext) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason) sig m, SQ.Sequent t c d, Applicative i) => (forall j . Applicative j => (i ~> j) -> (j t :@ Quantity :==> Type) -> (j c :@ Quantity :==> Type) -> (Type <==: m (j d))) -> Type <==: m (i t)
lamS f = runC $ SQ.lamRA $ \ wk a k -> C $ Check $ \ _T -> do
  (_, q, _A, _B) <- assertTacitFunction _T
  check (f wk (a :@ q :==> _A) (k :@ q :==> _B) ::: _B)

app :: (Has (Reader ElabContext) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason) sig m, Has (Writer Usage) sig m) => (a -> b -> c) -> (HasCallStack => m (a :==> Type)) -> (HasCallStack => Type <==: m b) -> m (c :==> Type)
app mk operator operand = do
  f' :==> _F <- operator
  (_, q, _A, _B) <- assertFunction _F
  a' <- censor @Usage (q ><<) $ check (operand ::: _A)
  pure $ mk f' a' :==> _B

appS :: (HasCallStack, Has (Reader ElabContext) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason) sig m, Has (Writer Usage) sig m, SQ.Sequent t c d, Applicative i) => (HasCallStack => m (i t :==> Type)) -> (HasCallStack => Type <==: m (i t)) -> m (i t :==> Type)
appS f a = do
  f' :==> _F <- f
  (_, q, _A, _B) <- assertFunction _F
  a' <- censor @Usage (q ><<) $ check (a ::: _A)
  (:==> _B) <$> SQ.µRA (\ wk k -> pure (wk f') SQ..||. SQ.lamLA (pure (wk a')) (pure k))


string :: Applicative m => Text -> m (Term :==> Type)
string s = pure $ E.String s :==> T.String

stringS :: (Applicative m, SQ.Sequent t c d, Applicative i) => Text -> m (i t :==> Type)
stringS s = SQ.stringRA s ==> pure T.String


let' :: (Has (Reader ElabContext) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason) sig m, Has (Writer Usage) sig m) => Bind m (Pattern (Name :==> Type)) -> m (Term :==> Type) -> Type <==: m Term -> Type <==: m Term
let' p a b = Check $ \ _B -> do
  a' :==> _A <- a
  (p', b') <- bind (p ::: (Many, _A)) (check (b ::: _B))
  pure $ Let p' a' b'


comp :: (Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason) sig m, Has (Writer Usage) sig m) => Type <==: m Term -> Type <==: m Term
comp b = Check $ \ _T -> do
  (sig, _B) <- assertComp _T
  graph <- ask
  module' <- ask
  let interfacePattern :: Has (Throw ErrReason) sig m => Interface Type -> m (RName :=: (Name :==> Type))
      interfacePattern (Interface n _) = maybe (freeVariable (toQ n)) (\ (n' :=: _T) -> pure ((n .:. n') :=: (n' :==> _T))) (listToMaybe (scopeToList . tm =<< unDInterface . def =<< lookupQ graph module' (toQ n)))
  p' <- traverse interfacePattern (interfaces sig)
  -- FIXME: can we apply quantities to dictionaries? what would they mean?
  b' <- (Many, PDict p') |- check (b ::: _B)
  pure $ E.Comp (map (fmap proof) p') b'


-- Pattern combinators

wildcardP :: Bind m (Pattern (Name :==> Type))
wildcardP = Bind $ \ _T k -> k PWildcard

varP :: Name -> Bind m (Pattern (Name :==> Type))
varP n = Bind $ \ _A k -> k (PVar (n :==> wrap _A))
  where
  wrap = \case
    T.Comp sig _A -> T.Arrow Nothing Many (T.Ne (Global (NE.FromList ["Data", "Unit"] :.: U "Unit")) Nil) (T.Comp sig _A)
    _T            -> _T

conP :: (Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason) sig m, Has (Writer Usage) sig m) => QName -> [Bind m (Pattern (Name :==> Type))] -> Bind m (Pattern (Name :==> Type))
conP n fs = Bind $ \ _A k -> do
  n' :=: _ ::: _T <- resolveC n
  _T' <- maybe (pure _T) (foldl' (\ _T _A -> do t <- _T ; (_, _, b) <- assertQuantifier t ; pure (b _A)) (pure _T) . snd) (unNeutral _A)
  fs' <- runBind (fieldsP fs) _T' (\ (fs, _T) -> fs <$ unify (Exp _A) (Act _T))
  k $ PCon n' (fromList fs')

fieldsP :: Has (Throw ErrReason) sig m => [Bind m a] -> Bind m ([a], Type)
fieldsP = foldr cons nil
  where
  cons p ps = Bind $ \ _A k -> do
    (_, _, _A', _A'') <- assertFunction _A
    runBind p _A' $ \ p' -> runBind ps _A'' (k . first (p' :))
  nil = Bind $ \ _T k -> k ([], _T)


allP :: Has (Throw ErrReason :+: Write Warn) sig m => Name -> Bind m (Pattern (Name :==> Type))
allP n = Bind $ \ _A k -> do
  (sig, _T) <- assertComp _A
  k (PVar (n :==> T.Arrow Nothing Many (T.Ne (Global (NE.FromList ["Data", "Unit"] :.: U "Unit")) Nil) (T.Comp sig _T)))


-- Expression elaboration

synthExpr :: (HasCallStack, Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason :+: Write Warn) sig m, Has (Writer Usage) sig m) => S.Ann S.Expr -> m (Term :==> Type)
synthExpr = let ?callStack = popCallStack GHC.Stack.callStack in withSpan $ \case
  S.Var n    -> var n
  S.App f a  -> synthApp f a
  S.As t _T  -> synthAs t _T
  S.String s -> string s
  S.Hole{}   -> nope
  S.Lam{}    -> nope
  where
  nope = couldNotSynthesize
  synthApp :: (Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason :+: Write Warn) sig m, Has (Writer Usage) sig m) => S.Ann S.Expr -> S.Ann S.Expr -> m (Term :==> Type)
  synthApp f a = app App (synthExpr f) (checkExpr a)
  synthAs :: (HasCallStack, Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason :+: Write Warn) sig m, Has (Writer Usage) sig m) => S.Ann S.Expr -> S.Ann S.Type -> m (Term :==> Type)
  synthAs t _T = as (checkExpr t ::: do { _T :==> _K <- synthType _T ; (:==> _K) <$> evalTExpr _T })


checkExpr :: (HasCallStack, Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason :+: Write Warn) sig m, Has (Writer Usage) sig m) => S.Ann S.Expr -> Type <==: m Term
checkExpr expr = let ?callStack = popCallStack GHC.Stack.callStack in withSpanC expr $ \case
  S.Hole n   -> hole n
  S.Lam cs   -> checkLam cs
  S.Var{}    -> switch (synthExpr expr)
  S.App{}    -> switch (synthExpr expr)
  S.As{}     -> switch (synthExpr expr)
  S.String{} -> switch (synthExpr expr)

checkLam :: (HasCallStack, Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason :+: Write Warn) sig m, Has (Writer Usage) sig m) => [S.Clause] -> Type <==: m Term
checkLam cs = lam (snd vs)
  where
  vs :: (Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason :+: Write Warn) sig m, Has (Writer Usage) sig m) => ([QName :=: (Type <==: m Term)], [(Bind m (Pattern (Name :==> Type)), Type <==: m Term)])
  vs = partitionEithers (map (\ (S.Clause (S.Ann _ _ p) b) -> case p of
    S.PVal p                          -> Right (bindPattern p, checkExpr b)
    S.PEff (S.Ann s _ (S.POp n fs k)) -> Left $ n :=: Check (\ _T -> pushSpan s (foldr (lam1 . bindPattern) (checkExpr b) (fromList fs:>k) <==: _T))) cs)


-- FIXME: check for unique variable names
bindPattern :: (HasCallStack, Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason :+: Write Warn) sig m, Has (Writer Usage) sig m) => S.Ann S.ValPattern -> Bind m (Pattern (Name :==> Type))
bindPattern = withSpanB $ \case
  S.PWildcard -> wildcardP
  S.PVar n    -> varP n
  S.PCon n ps -> conP n (map bindPattern ps)


-- | Elaborate a type abstracted over a kind’s parameters.
--
-- This is used to elaborate data constructors & effect operations, which receive the type/interface's kind's parameters as implicit parameters ahead of their own explicit ones.
abstractType :: Has (Reader ElabContext) sig m => m TX.Type -> Kind -> m TX.Type
abstractType body = \case
  KArrow (Just n) a b -> TX.ForAll n a <$> (n :==> a ||- abstractType body b)
  _                   -> body

abstractTerm :: (Has (Reader ElabContext) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason :+: Write Warn) sig m, Has (Writer Usage) sig m) => (Snoc TX.Type -> Snoc Term -> Term) -> Type <==: m Term
abstractTerm body = go Nil Nil
  where
  go ts fs = Check $ \case
    T.ForAll n   _T _B -> do
      d <- depth
      check (tlam (go (ts :> LName (getUsed d) n) fs) ::: T.ForAll n _T _B)
    T.Arrow  n q _A _B -> do
      d <- depth
      check (lam [(patternForArgType _A (fromMaybe __ n), go ts (fs :> \ d' -> Var (Free (LName (toIndexed d' (getUsed d)) (fromMaybe __ n)))))] ::: T.Arrow n q _A _B)
    _T                 -> do
      d <- depth
      pure $ body (TX.Var . Free . Right . toIndexed d <$> ts) (fs <*> pure d)

patternForArgType :: Has (Throw ErrReason :+: Write Warn) sig m => Type -> Name -> Bind m (Pattern (Name :==> Type))
patternForArgType = \case
  T.Comp{} -> allP
  _        -> varP


-- Declarations

elabDataDef
  :: (HasCallStack, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (Throw ErrReason :+: Write Warn) sig m)
  => [S.Ann (Name ::: S.Ann S.Type)]
  -> Kind <==: m [Name :=: Def]
-- FIXME: check that all constructors return the datatype.
elabDataDef constructors = Check $ \ _K -> do
  mname <- view name_
  for constructors $ \ (S.Ann _ _ (n ::: t)) -> do
    c_T <- elabType $ abstractType (Type.switch (synthType t) <==: KType) _K
    con' <- elabTerm $ check (abstractTerm (const (Con (mname :.: n) . toList)) ::: c_T)
    pure $ n :=: DTerm (Just con') c_T

elabInterfaceDef
  :: (HasCallStack, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (Throw ErrReason :+: Write Warn) sig m)
  => [S.Ann (Name ::: S.Ann S.Type)]
  -> Kind <==: m [Name :=: Type]
elabInterfaceDef constructors = Check $ \ _K -> do
  for constructors $ \ (S.Ann _ _ (n ::: t)) -> do
    _K' <- elabType $ abstractType (Type.switch (synthType t) <==: KType) _K
    pure $ n :=: _K'

-- FIXME: add a parameter for the effect signature.
elabTermDef
  :: (HasCallStack, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (Throw ErrReason :+: Write Warn) sig m)
  => S.Ann S.Expr
  -> Type <==: m Term
elabTermDef expr@(S.Ann s _ _) = Check $ \ _T -> do
  elabTerm $ pushSpan s $ check (go (checkExpr expr) ::: _T)
  where
  go k = Check $ \ _T -> case _T of
    T.ForAll{}               -> check (tlam (go k) ::: _T)
    T.Arrow (Just n) q _A _B -> check (lam [(varP n, go k)] ::: T.Arrow Nothing q _A _B)
    -- FIXME: this doesn’t do what we want for tacit definitions, i.e. where _T is itself a telescope.
    -- FIXME: eta-expanding here doesn’t help either because it doesn’t change the way elaboration of the surface term occurs.
    -- we’ve exhausted the named parameters; the rest is up to the body.
    _                        -> check (k ::: _T)


-- Modules

elabModule
  :: (HasCallStack, Has (Reader Graph :+: Reader Source :+: Throw ErrReason :+: Write Warn) sig m)
  => S.Ann S.Module
  -> m Module
elabModule (S.Ann _ _ (S.Module mname is os ds)) = execState (Module mname [] os (Scope mempty)) $ do
  let (importedNames, imports) = mapAccumL (\ names (S.Ann _ _ S.Import{ name }) -> (Set.insert name names, Import name)) Set.empty is
  imports_ .= imports

  local (`restrict` importedNames) $ do
    -- FIXME: maybe figure out the graph for mutual recursion?
    -- FIXME: check for redundant naming

    let elabScope :: (Has (State Module) sig m, Monoid a) => Name -> Prism' Submodule a -> Kind -> Kind <==: ReaderC Module m b -> (b -> m a) -> m ()
        elabScope dname p _K elab ret = letrec (scope_.decls_) dname (_DSubmodule.tm_.p) (DSubmodule (review p mempty) _K) (runModule (elab <==: _K) >>= ret)

    -- elaborate all the types first
    es <- for ds $ \ (S.Ann _ _ (dname, S.Ann _ _ def)) -> case def of
      S.DataDef cs _K -> Nothing <$ elabScope dname _SData _K (elabDataDef cs) (\ cs -> do
        scopeFromList cs <$ for_ cs (\ (dname :=: decl) -> scope_.decls_.at dname .= Just decl))

      S.InterfaceDef os _K -> Nothing <$ elabScope dname _SInterface _K (elabInterfaceDef os) (pure . scopeFromList)

      S.TermDef t tele -> do
        _T <- runModule $ elabType $ Type.switch (synthType tele) <==: KType
        scope_.decls_.at dname .= Just (DTerm Nothing _T)
        pure (Just (dname, t, _T))

    -- then elaborate the terms
    for_ (catMaybes es) $ \ (dname, t, _T) -> do
      t' <- runModule $ elabTermDef t <==: _T
      scope_.decls_.ix dname .= DTerm (Just t') _T

letrec :: (Has (State s) sig m, At a) => Setter' s a -> At.Index a -> Traversal' (IxValue a) b -> IxValue a -> m b -> m ()
letrec getter key projection initial final = do
  getter.at key .= Just initial
  getter.ix key.projection <~ final


-- Errors

assertQuantifier :: Has (Throw ErrReason) sig m => Type -> m (Name, Kind, Type -> Type)
assertQuantifier = assertMatch mismatchTypes _ForAll "{_} -> _"

-- | Expect a tacit (non-variable-binding) function type.
assertTacitFunction :: Has (Throw ErrReason) sig m => Type -> m (Maybe Name, Quantity, Type, Type)
assertTacitFunction = assertMatch mismatchTypes _Arrow "_ -> _"

-- | Expect a computation type with effects.
assertComp :: Has (Throw ErrReason) sig m => Type -> m (Signature Type, Type)
assertComp = assertMatch mismatchTypes _Comp "[_] _"


-- Elaboration

runModule :: Has (State Module) sig m => ReaderC Module m a -> m a
runModule m = do
  mod <- get
  runReader mod m

withSpanB :: Has (Reader ElabContext) sig m => (a -> Bind m b) -> S.Ann a -> Bind m b
withSpanB k (S.Ann s _ a) = Bind (\ _A k' -> pushSpan s (runBind (k a) _A k'))

withSpanC :: Has (Reader ElabContext) sig m => S.Ann a -> (a -> Type <==: m b) -> Type <==: m b
withSpanC (S.Ann s _ a) k = Check (\ _T -> pushSpan s (k a <==: _T))

withSpan :: Has (Reader ElabContext) sig m => (a -> m b) -> S.Ann a -> m b
withSpan k (S.Ann s _ a) = pushSpan s (k a)

provide :: (Has (Reader ElabContext) sig m, Has (State (Subst Type)) sig m) => Signature Type -> m a -> m a
provide sig m = do
  subst <- get
  env <- views context_ toEnv
  locally sig_ (mapSignature (apply subst env) sig :) m

require :: (Has (Reader ElabContext) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason) sig m, Has (Writer Usage) sig m) => Signature Type -> m ()
require req = do
  prv <- view sig_
  for_ (interfaces req) $ \ i -> findMaybeA (findMaybeA (runUnifyMaybe . unifyInterface i) . interfaces) prv >>= \case
    Nothing -> missingInterface i
    Just _  -> pure ()

findMaybeA :: (Foldable t, Applicative m) => (a -> m (Maybe b)) -> t a -> m (Maybe b)
findMaybeA p = getAp . fmap getFirst . foldMap (Ap . fmap First . p)


-- Judgements

check :: (Has (Reader ElabContext) sig m, Has (State (Subst Type)) sig m) => ((Type <==: m a) ::: Type) -> m a
check (m ::: _T) = case _T of
  T.Comp sig _T -> provide sig $ m <==: _T
  _T            -> m <==: _T


bind :: (Has (Reader ElabContext) sig m, Has (Throw ErrReason) sig m, Has (Writer Usage) sig m) => Bind m (Pattern (Name :==> Type)) ::: (Quantity, Type) -> m b -> m (Pattern Name, b)
bind (p ::: (q, _T)) m = runBind p _T (\ p' -> (proof <$> p',) <$> ((q, p') |- m))

newtype Bind m a = Bind { runBind :: forall x . Type -> (a -> m x) -> m x }
  deriving (Functor)
