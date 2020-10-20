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
  -- * Types
, elabType
, _Type
, (>~>)
  -- * Expressions
, elabExpr
, ($$)
, lam
  -- * Declarations
, elabDecl
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
import           Control.Effect.Sum
import           Data.Bifunctor (bimap, first)
import           Data.Foldable (foldl')
import qualified Data.IntMap as IntMap
import           Data.List.NonEmpty (NonEmpty(..), nonEmpty)
import           Data.Traversable (for, mapAccumL)
import           Facet.Context
import           Facet.Core hiding (global, ($$))
import qualified Facet.Core as C
import qualified Facet.Env as Env
import           Facet.Name hiding (L, R)
import           Facet.Span (Span(..))
import           Facet.Stack hiding ((!?))
import qualified Facet.Surface as S
import           Facet.Syntax
import           GHC.Stack
import           Text.Parser.Position (Spanned)

type Type = Value
type Expr = Value
type Prob = Value

type Subst = IntMap.IntMap (Maybe Prob ::: Type)

newtype Elab a = Elab { runElab :: forall sig m . Has (Reader (Context Type) :+: Reader (Env.Env Type) :+: Reader Span :+: State Subst :+: Throw Err) sig m => m a }

instance Functor Elab where
  fmap f (Elab m) = Elab (fmap f m)

instance Applicative Elab where
  pure a = Elab $ pure a
  Elab f <*> Elab a = Elab (f <*> a)

instance Monad Elab where
  Elab m >>= f = Elab $ m >>= runElab . f

instance Algebra (Reader (Context Type) :+: Reader (Env.Env Type) :+: Reader Span :+: State Subst :+: Throw Err) Elab where
  alg hdl sig ctx = case sig of
    L rctx              -> Elab $ alg (runElab . hdl) (inj rctx) ctx
    R (L renv)          -> Elab $ alg (runElab . hdl) (inj renv) ctx
    R (R (L rspan))     -> Elab $ alg (runElab . hdl) (inj rspan) ctx
    R (R (R (L subst))) -> Elab $ alg (runElab . hdl) (inj subst) ctx
    R (R (R (R throw))) -> Elab $ alg (runElab . hdl) (inj throw) ctx

elab :: Has (Reader Span :+: State (Env.Env Type) :+: Throw Err) sig m => Elab Value -> m Value
elab = elabWith apply

elabWith :: Has (Reader Span :+: State (Env.Env Type) :+: Throw Err) sig m => (Subst -> a -> m b) -> Elab a -> m b
elabWith f = runSubstWith f . runContext . Env.runEnv @Type . runElab


newtype Check a = Check { runCheck :: Type -> Elab a }
  deriving (Algebra (Reader Type :+: Reader (Context Type) :+: Reader (Env.Env Type) :+: Reader Span :+: State Subst :+: Throw Err), Applicative, Functor, Monad) via ReaderC Type Elab

newtype Synth a = Synth { synth :: Elab (a ::: Type) }

instance Functor Synth where
  fmap f (Synth m) = Synth (first f <$> m)

check :: (Check a ::: Type) -> Elab a
check = uncurryAnn runCheck


checkElab :: (Maybe Type -> Elab (a ::: Type)) -> Check a
checkElab f = tm <$> Check (f . Just)

synthElab :: (Maybe Type -> Elab (a ::: Type)) -> Synth a
synthElab f = Synth (f Nothing)


unify :: Type :===: Type -> Elab Type
unify (t1 :===: t2) = go (t1 :===: t2)
  where
  go = \case
    -- FIXME: this is missing a lot of cases
    VType                 :===: VType                 -> pure VType
    -- FIXME: resolve globals to try to progress past certain inequalities
    VNeut h1 e1           :===: VNeut h2 e2
      | h1 == h2
      , Just e' <- unifyS (e1 :===: e2)               -> VNeut h1 <$> e'
    VNeut (Metavar v) Nil :===: x                     -> solve (tm v :=: x)
    x                     :===: VNeut (Metavar v) Nil -> solve (tm v :=: x)
    VForAll t1 b1         :===: VForAll t2 b2
      | pl (tm t1) == pl (tm t2) -> do
        t <- go (ty t1 :===: ty t2)
        d <- asks @(Context Type) level
        let v = free d
        b <- go (b1 v :===: b2 v)
        pure $ VForAll (tm t1 ::: t) (\ v -> C.bind d v b)
    -- FIXME: build and display a diff of the root types
    t1                    :===: t2                    -> couldNotUnify t1 t2

  unifyS (Nil           :===: Nil)           = Just (pure Nil)
  -- NB: we make no attempt to unify case eliminations because they shouldn’t appear in types anyway.
  unifyS (i1 :> EApp l1 :===: i2 :> EApp l2)
    | pl l1 == pl l2                         = liftA2 (:>) <$> unifyS (i1 :===: i2) <*> Just (EApp . P (pl l1) <$> go (out l1 :===: out l2))
  unifyS _                                   = Nothing

  solve (n :=: val') = do
    subst <- get
    -- FIXME: occurs check
    case subst IntMap.! getMeta n of
      Just val ::: _T -> go (val' :===: val)
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
instantiate :: Expr ::: Type -> Elab (Expr ::: Type)
instantiate (e ::: _T) = case unForAll _T of
  Just (P Im _ ::: _T, _B) -> do
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

resolve
  :: DName
  -> Synth QName
resolve n = Synth $ Env.lookup n <$> ask >>= \case
  Just (m :=: _ ::: _T) -> pure $ m :.: n ::: _T
  Nothing
    | E (EName n) <- n  -> synth (resolve (C (CName n)))
    | otherwise         -> freeVariable Nothing n

resolveQ
  :: QName
  -> Synth QName
resolveQ q@(m :.: n) = Synth $ Env.lookupQ q <$> ask >>= \case
  Just (_ ::: _T) -> pure $ q ::: _T
  Nothing
    | E (EName n) <- n  -> synth (resolveQ (m :.: C (CName n)))
    | otherwise         -> freeVariable (Just m) n

-- FIXME: we’re instantiating when inspecting types in the REPL.
global
  :: Synth QName
  -> Synth Value
global n = Synth $ do
  q <- synth n
  instantiate (C.global q ::: ty q)

bound
  :: Index
  -> Synth Value
bound n = Synth $ ask >>= \ ctx -> case ctx !? n of
  -- FIXME: do we need to instantiate here to deal with rank-n applications?
  Just (_ ::: _T) -> pure (free (indexToLevel (level ctx) n) ::: _T)
  Nothing         -> err $ BadContext n

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
  a' <- check (a ::: ty _A)
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
  -> (t Value -> m Value)
  -> m (t Value -> Value)
p |-* b = do
  ctx <- ask @(Context Type)
  let d = level ctx
      ((_, ext), p') = mapAccumL (\ (d, ctx) t -> ((succ d, ctx . (|> t)), free d)) (d, id) p
  b' <- local ext (b p')
  pure $ \ p -> snd (foldl' (\ (d, b') v -> (succ d, C.bind d v b')) (succ d, b') p)

infix 1 |-*


-- Types

elabType
  :: HasCallStack
  => Spanned S.Type
  -> Maybe Type
  -> Elab (Type ::: Type)
elabType = withSpan' $ \case
  S.TQual  q -> switch $ global (resolveQ q)
  S.TFree  n -> switch $ global (resolve n)
  S.TBound n -> switch $ bound n
  S.THole  n -> check (hole n) "hole"
  S.Type     -> switch $ _Type
  t S.:=> b  -> switch $ bimap im (checkElab . elabType) t >~> \ v -> v |- checkElab (elabType b)
  f S.:$$ a  -> switch $ synthElab (elabType f) $$  checkElab (elabType a)
  a S.:-> b  -> switch $ ex __ ::: checkElab (elabType a) >~> \ _ -> checkElab (elabType b)
  where
  check m msg _T = expectChecked _T msg >>= \ _T -> (::: _T) <$> runCheck m _T


_Type :: Synth Type
_Type = Synth $ pure $ VType ::: VType

(>~>)
  :: (Pl_ UName ::: Check Type)
  -> (UName ::: Type -> Check Type)
  -> Synth Type
(n ::: t) >~> b = Synth $ do
  _T <- check (t ::: VType)
  b' <- elabBinder $ \ _ -> check (b (out n ::: _T) ::: VType)
  pure $ VForAll (n ::: _T) b' ::: VType

infixr 1 >~>


-- Expressions

elabExpr
  :: HasCallStack
  => Spanned S.Expr
  -> Maybe Type
  -> Elab (Expr ::: Type)
elabExpr = withSpan' $ \case
  S.Qual  q -> switch $ global (resolveQ q)
  S.Free  n -> switch $ global (resolve n)
  S.Bound n -> switch $ bound n
  S.Hole  n -> check (hole n) "hole"
  f S.:$  a -> switch $ synthElab (elabExpr f) $$ checkElab (elabExpr a)
  S.Comp cs -> check (elabComp cs) "computation"
  where
  check m msg _T = expectChecked _T msg >>= \ _T -> (::: _T) <$> runCheck m _T


lam
  :: Pl_ UName
  -> (UName ::: Type -> Check Expr)
  -> Check Expr
lam n b = Check $ \ _T -> do
  (_ ::: _T, _B) <- expectQuantifier "when checking lambda" _T
  b' <- elabBinder $ \ v -> check (b (out n ::: _T) ::: _B v)
  pure $ VLam (n ::: _T) b'


elabComp
  :: HasCallStack
  => Spanned S.Comp
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

elabClauses :: [(NonEmpty (Spanned S.Pattern), Spanned S.Expr)] -> Check Expr
elabClauses [((_, S.PVar n):|ps, b)] = Check $ \ _T -> do
  (P pl _ ::: _A, _B) <- expectQuantifier "when checking clauses" _T
  b' <- elabBinder $ \ v -> n ::: _A |- check (maybe (checkElab (elabExpr b)) (elabClauses . pure . (,b)) (nonEmpty ps) ::: _B v)
  pure $ VLam (P pl n ::: _A) b'
-- FIXME: this is incorrect in the presence of wildcards (or something). e.g. { (true) (true) -> true, _ _ -> false } gets the inner {(true) -> true} clause from the first case appended to the
elabClauses cs = Check $ \ _T -> do
  rest <- case foldMap partitionClause cs of
    XB    -> pure $ Nothing
    XL _  -> pure $ Nothing
    XR cs -> pure $ Just cs
    XT    -> error "mixed" -- FIXME: throw a proper error
  (_ ::: _A, _B) <- expectQuantifier "when checking clauses" _T
  b' <- elabBinder $ \ v -> do
    let _B' = _B v
    cs' <- for cs $ \ (p:|_, b) -> do
      p' <- check (elabPattern p ::: _A)
      b' <- p' |-* \ _ -> check (maybe (checkElab (elabExpr b)) elabClauses rest ::: _B')
      pure (p', b')
    pure $ case' v cs'
  pure $ VLam (ex __ ::: _A) b'
  where
  partitionClause (_:|ps, b) = case ps of
    []   -> XL ()
    p:ps -> XR [(p:|ps, b)]


elabPattern
  :: Spanned S.Pattern
  -> Check (C.Pattern Type (UName ::: Type))
elabPattern = withSpan $ \case
  S.PVar n    -> Check $ \ _T -> pure (C.PVar (n ::: _T))
  S.PCon n ps -> Check $ \ _T -> do
    q ::: _T' <- synth (resolve (C n))
    let go _T' = \case
          Nil   -> Nil <$ unify (_T' :===: _T)
          ps:>p -> do
            (_A, _B) <- expectQuantifier "when checking constructor pattern" _T'
            -- FIXME: there’s no way this is going to work, let alone a good idea
            -- FIXME: elaborate patterns in CPS, binding locally with elabBinder, & obviating the need for |-*.
            v <- metavar <$> meta (ty _A)
            ps' <- go (_B v) ps
            p' <- check (elabPattern p ::: ty _A)
            pure $ ps' :> p'
    C.PCon . Con (q ::: _T') <$> go _T' ps


-- Declarations

elabDecl
  :: HasCallStack
  => Spanned S.Decl
  -> Check (Either [CName ::: Type] Value) ::: Check Type
elabDecl d = withSpans d $ \case
  S.DDecl d -> first (fmap Left)  (elabDDecl d)
  S.TDecl t -> first (fmap Right) (elabTDecl t)

elabDDecl
  :: HasCallStack
  => Spanned S.DDecl
  -> Check [CName ::: Type] ::: Check Type
elabDDecl d = go d id
  where
  go
    :: Spanned S.DDecl
    -> (Check Value -> Check Value)
    -> Check [CName ::: Type] ::: Check Type
  go d km = withSpans d $ \case
    S.DDForAll (n ::: t) b ->
      let b' ::: _B = go b
            (km . (\ b  -> Check $ \ _T -> do
              (_ ::: _T, _B) <- expectQuantifier "in type quantifier" _T
              b' <- elabBinder $ \ _ -> check ((out n ::: _T |- b) ::: VType)
              pure $ VForAll (im (out n) ::: _T) b'))
      in b' ::: checkElab (switch (n ::: checkElab (elabType t) >~> (|- _B)))

    S.DDBody t b -> elabData km b ::: checkElab (elabType t)

  -- FIXME: check that all constructors return the datatype.
  elabData k cs = for cs $ withSpan $ \ (n ::: t) -> (n :::) <$> k (checkElab (elabType t))


elabTDecl
  :: HasCallStack
  => Spanned S.TDecl
  -> Check Value ::: Check Type
elabTDecl d = go d
  where
  go
    :: Spanned S.TDecl
    -> Check Value ::: Check Type
  go d = withSpans d $ \case
    S.TDForAll (n ::: t) b ->
      let b' ::: _B = go b
      in lam n (|- b') :::
          checkElab (switch (__ <$ n ::: checkElab (elabType t) >~> (|- _B)))

    S.TDBody t b -> checkElab (elabExpr b) ::: checkElab (elabType t)


-- Modules

elabModule
  :: forall m sig
  .  (HasCallStack, Has (Throw Err) sig m)
  => Spanned S.Module
  -> m (Env.Env Type, C.Module)
elabModule (s, S.Module mname _is ds) = runReader s . runState (fmap pure . (,)) (mempty @(Env.Env Type)) $ do
  -- FIXME: trace the defs as we elaborate them
  -- FIXME: elaborate all the types first, and only then the terms
  -- FIXME: maybe figure out the graph for mutual recursion?
  defs <- for ds $ \ (s, (n, d)) -> setSpan s $ do
    let qname = mname :.: n
        e ::: t = elabDecl d

    _T <- elab $ check (t ::: VType)

    modify $ Env.insert (qname :=: Nothing ::: _T)

    (s, e') <- elabWith (fmap pure . (,)) $ check (e ::: _T)
    case e' of
      Left cs  -> do
        cs' <- for cs $ \ (n ::: _T) -> do
          _T' <- apply s _T
          let go fs = \case
                VForAll _T _B -> VLam _T (\ v -> go (fs :> v) (_B v))
                _T            -> VCon (Con (mname :.: C n ::: _T) fs)
          c <- apply s (go Nil _T')
          modify $ Env.insert (mname :.: C n :=: Just c ::: _T')
          pure $ n ::: _T'
        pure (qname, C.DData cs' ::: _T)
      Right e' -> do
        e'' <- apply s e'
        modify $ Env.insert (qname :=: Just e'' ::: _T)
        pure (qname, C.DTerm e'' ::: _T)

  pure $ C.Module mname [] defs


-- | Apply the substitution to the value.
apply :: Applicative m => Subst -> Value -> m Value
apply s v = pure $ subst (IntMap.mapMaybe tm s) v -- FIXME: error if the substitution has holes.

emptySubst :: Subst
emptySubst = IntMap.empty

runSubstWith :: (Subst -> a -> m b) -> StateC Subst m a -> m b
runSubstWith with = runState with emptySubst

runContext :: ReaderC (Context Type) m a -> m a
runContext = runReader empty


-- Errors

setSpan :: Has (Reader Span) sig m => Span -> m a -> m a
setSpan = local . const

withSpan :: Has (Reader Span) sig m => (a -> m b) -> (Span, a) -> m b
withSpan k (s, a) = setSpan s (k a)

withSpan' :: Has (Reader Span) sig m => (a -> b -> m c) -> (Span, a) -> b -> m c
withSpan' k (s, a) b = setSpan s (k a b)

withSpans :: Has (Reader Span) sig m => (Span, a) -> (a -> m b ::: m c) -> m b ::: m c
withSpans (s, d) f = let t ::: _T = f d in setSpan s t ::: setSpan s _T


data Err = Err
  { span    :: Span
  , reason  :: Reason
  , context :: Context Type
  }

data Reason
  = FreeVariable (Maybe MName) DName
  | CouldNotSynthesize String
  | Mismatch String (Either String Type) Type
  | Hole UName Type
  | BadContext Index


err :: Reason -> Elab a
err reason = do
  span <- ask
  ctx <- ask
  throwError $ Err span reason ctx

mismatch :: String -> Either String Type -> Type -> Elab a
mismatch msg exp act = err $ Mismatch msg exp act

couldNotUnify :: Type -> Type -> Elab a
couldNotUnify t1 t2 = mismatch "mismatch" (Right t2) t1

couldNotSynthesize :: String -> Elab a
couldNotSynthesize = err . CouldNotSynthesize

freeVariable :: Maybe MName -> DName -> Elab a
freeVariable m n = err $ FreeVariable m n

expectChecked :: Maybe Type -> String -> Elab Type
expectChecked t msg = maybe (couldNotSynthesize msg) pure t


-- Patterns

expectMatch :: (Type -> Maybe out) -> String -> String -> Type -> Elab out
expectMatch pat exp s _T = maybe (mismatch s (Left exp) _T) pure (pat _T)

expectQuantifier :: String -> Type -> Elab (Pl_ UName ::: Type, Type -> Type)
expectQuantifier = expectMatch unForAll "{_} -> _"
