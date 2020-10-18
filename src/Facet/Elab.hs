{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Facet.Elab
( M(..)
, Val
, Type
, Expr
, Elab(..)
, Check(..)
, Synth(..)
, check
, unify
  -- * General
, global
  -- * Types
, elabType
, _Type
, _Unit
, (.*)
, (-->)
, (>~>)
  -- * Expressions
, elabExpr
, ($$)
, tlam
, lam
, unit
, (**)
  -- * Declarations
, elabDecl
  -- * Modules
, elabModule
  -- * Errors
, ErrDoc
, Err(..)
, Reason(..)
) where

import           Control.Algebra
import           Control.Applicative (liftA2)
import           Control.Carrier.Error.Church
import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Effect.Parser.Span (Span(..))
import           Control.Effect.Sum
import           Data.Bifunctor (bimap, first)
import           Data.Foldable (foldl', toList)
import qualified Data.IntMap as IntMap
import           Data.List.NonEmpty (NonEmpty(..), nonEmpty)
import qualified Data.Text as T
import           Data.Traversable (for)
import           Facet.Context
import           Facet.Core hiding (global, ($$))
import qualified Facet.Core as C
import qualified Facet.Env as Env
import           Facet.Name hiding (L, R)
import           Facet.Stack hiding ((!?))
import qualified Facet.Surface as S
import           Facet.Syntax
import           GHC.Stack
import           Prelude hiding ((**))
import           Prettyprinter (Doc)
import           Prettyprinter.Render.Terminal (AnsiStyle)
import           Text.Parser.Position (Spanned)

type Val = Value
type Type = Value
type Expr = Value
type Prob = Value

newtype M v a = M { rethrow :: forall sig m . Has (State (Subst v) :+: Throw (Err v)) sig m => m a }

instance Functor (M v) where
  fmap f (M m) = M (fmap f m)

instance Applicative (M v) where
  pure a = M $ pure a
  M f <*> M a = M (f <*> a)

instance Monad (M v) where
  M m >>= f = M $ m >>= rethrow . f

instance Algebra (State (Subst v) :+: Throw (Err v)) (M v) where
  alg hdl sig ctx = case sig of
    L smctx -> M $ alg (rethrow . hdl) (inj smctx) ctx
    R throw -> M $ alg (rethrow . hdl) (inj throw) ctx


type Subst v = IntMap.IntMap (Maybe (Prob v) ::: Type v)

newtype Elab v a = Elab { elab :: forall sig m . Has (Reader (Env.Env (Type v)) :+: Reader (Context (Val v ::: Type v)) :+: Reader Span :+: State (Subst v) :+: Throw (Err v)) sig m => m a }

instance Functor (Elab v) where
  fmap f (Elab m) = Elab (fmap f m)

instance Applicative (Elab v) where
  pure a = Elab $ pure a
  Elab f <*> Elab a = Elab (f <*> a)

instance Monad (Elab v) where
  Elab m >>= f = Elab $ m >>= elab . f

instance Algebra (Reader (Env.Env (Type v)) :+: Reader (Context (Val v ::: Type v)) :+: Reader Span :+: State (Subst v) :+: Throw (Err v)) (Elab v) where
  alg hdl sig ctx = case sig of
    L renv              -> Elab $ alg (elab . hdl) (inj renv) ctx
    R (L rctx)          -> Elab $ alg (elab . hdl) (inj rctx) ctx
    R (R (L rspan))     -> Elab $ alg (elab . hdl) (inj rspan) ctx
    R (R (R (L smctx))) -> Elab $ alg (elab . hdl) (inj smctx) ctx
    R (R (R (R throw))) -> Elab $ alg (elab . hdl) (inj throw) ctx


askEnv :: Has (Reader (Env.Env (Type v))) sig (t v) => t v (Env.Env (Type v))
askEnv = ask

askContext :: Has (Reader (Context (Val v ::: Type v))) sig (t v) => t v (Context (Val v ::: Type v))
askContext = ask


newtype Check v a = Check { runCheck :: Type v -> Elab v a }
  deriving (Algebra (Reader (Type v) :+: Reader (Env.Env (Type v)) :+: Reader (Context (Val v ::: Type v)) :+: Reader Span :+: State (Subst v) :+: Throw (Err v)), Applicative, Functor, Monad) via ReaderC (Type v) (Elab v)

newtype Synth v a = Synth { synth :: Elab v (a ::: Type v) }

instance Functor (Synth v) where
  fmap f (Synth m) = Synth (first f <$> m)

check :: (Check v a ::: Type v) -> Elab v a
check = uncurryAnn runCheck


checkElab :: (Maybe (Type v) -> Elab v (a ::: Type v)) -> Check v a
checkElab f = tm <$> Check (f . Just)

synthElab :: (Maybe (Type v) -> Elab v (a ::: Type v)) -> Synth v a
synthElab f = Synth (f Nothing)


unify
  :: forall v
  .  Eq v
  => Type v :===: Type v
  -> Elab v (Type v)
unify (t1 :===: t2) = go (t1 :===: t2)
  where
  go
    :: Prob v :===: Prob v
    -> Elab v (Type v)
  go = \case
    -- FIXME: this is missing a lot of cases
    Type              :===: Type              -> pure Type
    Void              :===: Void              -> pure Void
    TUnit             :===: TUnit             -> pure TUnit
    Unit              :===: Unit              -> pure Unit
    -- FIXME: resolve globals to try to progress past certain inequalities
    Neut h1 e1        :===: Neut h2 e2
      | h1 == h2
      , Just e' <- unifyS (e1 :===: e2) -> Neut h1 <$> e'
    Neut (Meta v) Nil :===: x                 -> solve (tm v :=: x)
    x                 :===: Neut (Meta v) Nil -> solve (tm v :=: x)
    t1 :=> b1         :===: t2 :=> b2         -> do
      t <- go (ty t1 :===: ty t2)
      b <- out (tm t1) ::: t |- \ v -> do
        let b1' = b1 v
            b2' = b2 v
        go (b1' :===: b2')
      pure $ tm t1 ::: t :=> b
    TPrd l1 r1        :===: TPrd l2 r2        -> TPrd <$> go (l1 :===: l2) <*> go (r1 :===: r2)
    Prd  l1 r1        :===: Prd  l2 r2        -> Prd  <$> go (l1 :===: l2) <*> go (r1 :===: r2)
    -- FIXME: build and display a diff of the root types
    t1                :===: t2                -> couldNotUnify t1 t2

  unifyS (Nil          :===: Nil)          = Just (pure Nil)
  -- NB: we make no attempt to unify case eliminations because they shouldn’t appear in types anyway.
  unifyS (i1 :> App l1 :===: i2 :> App l2)
    | pl l1 == pl l2                       = liftA2 (:>) <$> unifyS (i1 :===: i2) <*> Just (App . P (pl l1) <$> go (out l1 :===: out l2))
  unifyS _                                 = Nothing

  solve :: Level :=: Prob v -> Elab v (Val v)
  solve (n :=: val') = do
    subst <- getSubst
    -- FIXME: occurs check
    case subst IntMap.! getLevel n of
      Just val ::: _T -> go (val' :===: val)
      Nothing  ::: _T -> val' <$ put (insertSubst n (Just val' ::: _T) subst)


meta :: Type v -> Elab v (Prob v)
meta _T = do
  subst <- getSubst
  let m = Level (length subst)
  put (insertSubst m (Nothing ::: _T) subst)
  pure $ metavar (m ::: _T)

insertSubst :: Level -> Maybe (Prob v) ::: Type v -> Subst v -> Subst v
insertSubst n (v ::: _T) = IntMap.insert (getLevel n) (v ::: _T)

getSubst :: Has (State (Subst v)) sig (t v) => t v (Subst v)
getSubst = get

-- FIXME: does instantiation need to be guided by the expected type?
instantiate :: Expr v ::: Type v -> Elab v (Expr v ::: Type v)
instantiate (e ::: _T) = case unForAll _T of
  Just (P Im _ ::: _T, _B) -> do
    m <- meta _T
    instantiate (e C.$$ im m ::: _B m)
  _                        -> pure $ e ::: _T


-- General

switch
  :: Eq v
  => Synth v (Val v)
  -> Maybe (Type v)
  -> Elab v (Val v ::: Type v)
switch (Synth m) = \case
  Just _K -> m >>= \ (a ::: _K') -> (a :::) <$> unify (_K' :===: _K)
  _       -> m

resolve
  :: DName
  -> Synth v QName
resolve n = Synth $ Env.lookup n <$> askEnv >>= \case
  Just (m :=: _ ::: _T) -> pure $ m :.: n ::: _T
  Nothing
    | E (EName n) <- n  -> synth (resolve (C (CName n)))
    | otherwise         -> freeVariable n

global
  :: DName
  -> Synth v (Val v)
global n = Synth $ do
  q <- synth (resolve n)
  instantiate (C.global q ::: ty q)

bound
  :: Context (Val v ::: Type v)
  -> Index
  -> Synth v (Val v)
bound ctx n = Synth $ case ctx !? n of
  -- FIXME: do we need to instantiate here to deal with rank-n applications?
  Just (_ ::: (v ::: _T)) -> pure (v ::: _T)
  Nothing                 -> err $ BadContext n

hole
  :: T.Text
  -> Check v a
hole n = Check $ \ _T -> err $ Hole n _T

($$)
  :: Synth v (Val v)
  -> Check v (Val v)
  -> Synth v (Val v)
f $$ a = Synth $ do
  f' ::: _F <- synth f
  (_A, _B) <- expectQuantifiedType "in application" _F
  a' <- check (a ::: ty _A)
  pure $ (f' C.$$ ex a') ::: _B a'


(|-)
  :: UName ::: Type v
  -> (Val v -> Elab v (Val v))
  -> Elab v (Val v -> Val v)
n ::: _T |- f = do
  ctx <- askContext
  handleBinder (level ctx) (\ v -> local (|> (n ::: v ::: _T)) (f v))

infix 1 |-

(|-*)
  :: C.Pattern (Type v) (UName ::: Type v)
  -> (C.Pattern (Type v) (Val v) -> Elab v (Val v))
  -> Elab v (C.Pattern (Type v) (Val v) -> Val v)
p |-* f = do
  ctx <- askContext
  handleBinderP (level ctx) p (\ v ->
    local (flip (foldl' (|>)) (zipWith (\ (n ::: _T) v -> n ::: v ::: _T) (toList p) (toList v))) (f v))

infix 1 |-*


-- Types

elabType
  :: (HasCallStack, Eq v)
  => Context (Val v ::: Type v)
  -> Spanned (S.Type a)
  -> Maybe (Type v)
  -> Elab v (Type v ::: Type v)
elabType ctx = withSpan' $ \case
  S.TFree  n -> switch $ global n
  S.TBound n -> switch $ bound ctx n
  S.THole  n -> check (hole n) "hole"
  S.Type     -> switch $ _Type
  S.Void     -> switch $ _Void
  S.TUnit    -> switch $ _Unit
  t S.:=> b  -> switch $ bimap im (checkElab . elabType ctx) t >~> \ v -> checkElab (elabType (ctx |> v) b)
  f S.:$$ a  -> switch $ synthElab (elabType ctx f) $$  checkElab (elabType ctx a)
  a S.:-> b  -> switch $ checkElab (elabType ctx a) --> checkElab (elabType ctx b)
  l S.:** r  -> switch $ checkElab (elabType ctx l) .*  checkElab (elabType ctx r)
  where
  check m msg _T = expectChecked _T msg >>= \ _T -> (::: _T) <$> runCheck m _T


_Type :: Synth v (Type v)
_Type = Synth $ pure $ Type ::: Type

_Void :: Synth v (Type v)
_Void = Synth $ pure $ Void ::: Type

_Unit :: Synth v (Type v)
_Unit = Synth $ pure $ Unit ::: Type

(.*)
  :: Check v (Type v)
  -> Check v (Type v)
  -> Synth v (Type v)
a .* b = Synth $ do
  a' <- check (a ::: Type)
  b' <- check (b ::: Type)
  pure $ (TPrd a' b') ::: Type

infixl 7 .*

(-->)
  :: Check v (Type v)
  -> Check v (Type v)
  -> Synth v (Type v)
a --> b = ex __ ::: a >~> const b

infixr 1 -->

(>~>)
  :: (Pl_ UName ::: Check v (Type v))
  -> (UName ::: Val v ::: Type v -> Check v (Type v))
  -> Synth v (Type v)
(n ::: t) >~> b = Synth $ do
  _T <- check (t ::: Type)
  b' <- out n ::: _T |- \ v -> check (b (out n ::: v ::: _T) ::: Type)
  pure $ (n ::: _T :=> b') ::: Type

infixr 1 >~>


-- Expressions

elabExpr
  :: (HasCallStack, Eq v)
  => Context (Val v ::: Type v)
  -> Spanned (S.Expr a)
  -> Maybe (Type v)
  -> Elab v (Expr v ::: Type v)
elabExpr ctx = withSpan' $ \case
  S.Free  n -> switch $ global n
  S.Bound n -> switch $ bound ctx n
  S.Hole  n -> check (hole n) "hole"
  f S.:$  a -> switch $ synthElab (elabExpr ctx f) $$ checkElab (elabExpr ctx a)
  l S.:*  r -> check (checkElab (elabExpr ctx l) ** checkElab (elabExpr ctx r)) "product"
  S.Unit    -> switch unit
  S.Comp cs -> check (elabComp ctx cs) "computation"
  where
  check m msg _T = expectChecked _T msg >>= \ _T -> (::: _T) <$> runCheck m _T


tlam
  :: UName
  -> (UName ::: Type v ::: Type v -> Check v (Expr v))
  -> Check v (Expr v)
tlam n b = Check $ \ ty -> do
  (_ ::: _T, _B) <- expectQuantifiedType "when checking type lambda" ty
  b' <- n ::: _T |- \ v -> check (b (n ::: v ::: _T) ::: _B v)
  pure (Lam (im n ::: _T) b')

lam
  :: UName
  -> (UName ::: Expr v ::: Type v -> Check v (Expr v))
  -> Check v (Expr v)
lam n b = Check $ \ _T -> do
  (_A, _B) <- expectQuantifiedType "when checking lambda" _T
  b' <- n ::: ty _A |- \ v -> check (b (n ::: v ::: ty _A) ::: _B v)
  pure (Lam (ex n ::: ty _A) b')

unit :: Synth v (Expr v)
unit = Synth . pure $ Unit ::: TUnit

(**)
  :: Check v (Expr v)
  -> Check v (Expr v)
  -> Check v (Expr v)
l ** r = Check $ \ _T -> do
  (_L, _R) <- expectProductType "when checking product" _T
  l' <- check (l ::: _L)
  r' <- check (r ::: _R)
  pure (Prd l' r')

elabComp
  :: (HasCallStack, Eq v)
  => Context (Val v ::: Type v)
  -> Spanned (S.Comp a)
  -> Check v (Expr v)
elabComp ctx = withSpan $ \case
  S.Expr    b  -> checkElab (elabExpr ctx b)
  S.Clauses cs -> elabClauses ctx cs

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

elabClauses :: Eq v => Context (Val v ::: Type v) -> [(NonEmpty (Spanned (S.Pattern UName)), Spanned (S.Expr a))] -> Check v (Expr v)
-- FIXME: do the same thing for wildcards
elabClauses ctx [((_, S.Var n):|ps, b)] = Check $ \ _T -> do
  (P pl _ ::: _A, _B) <- expectQuantifiedType "when checking clauses" _T
  b' <- n ::: _A |- \ v -> do
    let ctx' = ctx |> (n ::: v ::: _A)
    check (maybe (checkElab (elabExpr ctx' b)) (elabClauses ctx' . pure . (,b)) (nonEmpty ps) ::: _B v)
  pure $ Lam (P pl n ::: _A) b'
elabClauses ctx cs = Check $ \ _T -> do
  (P _ n ::: _A, _B) <- expectQuantifiedType "when checking clauses" _T
  rest <- case foldMap partitionClause cs of
    XB    -> pure $ Nothing
    XL _  -> pure $ Nothing
    XR cs -> pure $ Just cs
    XT    -> error "mixed" -- FIXME: throw a proper error
  b' <- n ::: _A |- \ v -> do
    let _B' = _B v
    cs' <- for cs $ \ (p:|_, b) -> do
      p' <- check (elabPattern p ::: _A)
      b' <- p' |-* \ v ->
        let ctx' = foldl' (|>) ctx (zipWith (\ (n ::: _T) v -> n ::: v ::: _T) (toList p') (toList v))
        in check (maybe (checkElab (elabExpr ctx' b)) (elabClauses ctx') rest ::: _B')
      pure (p', b')
    pure $ case' v cs'
  pure $ Lam (ex __ ::: _A) b'
  where
  partitionClause (_:|ps, b) = case ps of
    []   -> XL ()
    p:ps -> XR [(p:|ps, b)]


elabPattern
  :: Eq v
  => Spanned (S.Pattern UName)
  -> Check v (C.Pattern (Type v) (UName ::: Type v))
elabPattern = withSpan $ \case
  S.Wildcard -> pure C.Wildcard
  S.Var n    -> Check $ \ _T -> pure (C.Var (n ::: _T))
  S.Con n ps -> Check $ \ _T -> do
    q ::: _T' <- synth (resolve (C n))
    let go _T' = \case
          []   -> [] <$ unify (_T' :===: _T)
          p:ps -> do
            (_A, _B) <- expectQuantifiedType "when checking constructor pattern" _T'
            p' <- check (elabPattern p ::: ty _A)
            -- FIXME: there’s no way this is going to work, let alone a good idea
            v <- meta (ty _A)
            ps' <- go (_B v) ps
            pure $ p' : ps'
    C.Con (q ::: _T') <$> go _T' ps
  S.Tuple ps -> Check $ \ _T -> C.Tuple . toList <$> go _T (fromList ps)
    where
    go _T = \case
      Nil      -> case _T of
        TUnit -> pure Nil
        _     -> mismatch "when checking empty tuple pattern" (Right TUnit) _T
      Nil :> p -> (Nil :>) <$> check (elabPattern p ::: _T)
      ps  :> p -> do
        (_L, _R) <- expectProductType "when checking tuple pattern" _T
        (:>) <$> go _L ps <*> check (elabPattern p ::: _R)


-- Declarations

elabDecl
  :: forall a v
  .  (HasCallStack, Eq v)
  => Spanned (S.Decl a)
  -> (Context (Val v ::: Type v) -> Check v (Either [CName ::: Type v] (Val v))) ::: (Context (Val v ::: Type v) -> Check v (Type v))
elabDecl d = go d id id
  where
  go
    :: Spanned (S.Decl a)
    -> ((Context (Val v ::: Type v) -> Check v (Val v)) -> (Context (Val v ::: Type v) -> Check v (Val v)))
    -> ((Context (Val v ::: Type v) -> Check v (Val v)) -> (Context (Val v ::: Type v) -> Check v (Val v)))
    -> (Context (Val v ::: Type v) -> Check v (Either [CName ::: Type v] (Val v))) ::: (Context (Val v ::: Type v) -> Check v (Type v))
  go d km kt = withSpans d $ \case
    (n ::: t) S.:==> b ->
      go b
        (km . (\ b  ctx -> tlam n (b . (ctx |>))))
        (kt . (\ _B ctx -> checkElab (switch (im n ::: checkElab (elabType ctx t) >~> _B . (ctx |>)))))

    (n ::: t) S.:--> b ->
      go b
        (km . (\ b  ctx -> lam n (b . (ctx |>))))
        (kt . (\ _B ctx -> checkElab (switch (ex __ ::: checkElab (elabType ctx t) >~> _B . (ctx |>)))))

    t S.:= b -> (\ ctx -> elabDeclBody km ctx b) ::: kt (\ ctx -> checkElab (elabType ctx t))

  withSpans (s, d) f = let t ::: _T = f d in setSpan s . t ::: setSpan s . _T

elabDeclBody :: (HasCallStack, Eq v) => ((Context (Val v ::: Type v) -> Check v (Val v)) -> (Context (Val v ::: Type v) -> Check v (Val v))) -> Context (Val v ::: Type v) -> S.DeclBody a -> Check v (Either [CName ::: Type v] (Val v))
elabDeclBody k ctx = \case
  S.DExpr b -> Right <$> k (checkElab . (`elabExpr` b)) ctx
  S.DType b -> Right <$> k (checkElab . (`elabType` b)) ctx
  S.DData c -> Left <$> elabData k ctx c


elabData :: Eq v => ((Context (Val v ::: Type v) -> Check v (Val v)) -> (Context (Val v ::: Type v) -> Check v (Val v))) -> Context (Val v ::: Type v) -> [Spanned (CName ::: Spanned (S.Type a))] -> Check v [CName ::: Type v]
-- FIXME: check that all constructors return the datatype.
elabData k ctx cs = for cs $ withSpan $ \ (n ::: t) -> (n :::) <$> k (checkElab . (`elabType` t)) ctx


-- Modules

elabModule
  :: forall v a m sig
  .  (HasCallStack, Has (Throw (Err v)) sig m, Eq v)
  => Spanned (S.Module a)
  -> m (C.Module v)
elabModule (s, S.Module mname ds) = runReader s . evalState (mempty @(Env.Env (Type v))) $ do
  -- FIXME: elaborate all the types first, and only then the terms
  -- FIXME: maybe figure out the graph for mutual recursion?
  defs <- for ds $ \ (s, (n, d)) -> setSpan s $ do
    let qname = mname :.: n
        e ::: t = elabDecl d
    runContext $ do
      _T <- runEnv . runSubst . elab $ check (t empty ::: Type)

      modify $ Env.insert (qname :=: Nothing ::: _T)

      (s, e') <- runEnv . runState (fmap pure . (,)) emptySubst . elab $ check (e empty ::: _T)
      case e' of
        Left cs  -> do
          cs' <- for cs $ \ (n ::: _T) -> do
            let _T' = apply s _T
                go fs = \case
                  _T :=> _B -> Lam _T (\ v -> go (fs :> v) (_B v))
                  _T        -> VCon (mname :.: C n ::: _T) fs
            modify $ Env.insert (mname :.: C n :=: Just (apply s (go Nil _T')) ::: _T')
            pure $ n ::: _T'
          pure (qname, C.DData cs' ::: _T)
        Right (apply s -> e') -> do
          modify $ Env.insert (qname :=: Just e' ::: _T)
          pure (qname, C.DTerm e' ::: _T)

      -- FIXME: support defining types

  pure $ C.Module mname defs
  where
  -- Apply the substitution to the value.
  -- FIXME: error if the substitution has holes.
  apply s v = subst (IntMap.mapMaybe tm s) v
  emptySubst = IntMap.empty @(Maybe (Prob v) ::: Type v)

  runContext = runReader @(Context (Val v ::: Type v)) empty
  runSubst = runState (fmap pure . apply) emptySubst

  runEnv m = do
    env <- get @(Env.Env (Type v))
    runReader env m



-- Errors

setSpan :: Has (Reader Span) sig m => Span -> m a -> m a
setSpan = local . const

withSpan :: Has (Reader Span) sig m => (a -> m b) -> (Span, a) -> m b
withSpan k (s, a) = setSpan s (k a)

withSpan' :: Has (Reader Span) sig m => (a -> b -> m c) -> (Span, a) -> b -> m c
withSpan' k (s, a) b = setSpan s (k a b)


type ErrDoc = Doc AnsiStyle

data Err v = Err
  { span    :: Span
  , reason  :: Reason v
  , context :: Context (Val v ::: Type v)
  }

data Reason v
  = FreeVariable DName
  | CouldNotSynthesize String
  | Mismatch String (Either String (Type v)) (Type v)
  | Hole T.Text (Type v)
  | BadContext Index


err :: Has (Reader (Context (Val v ::: Type v)) :+: Reader Span :+: Throw (Err v)) sig (t v) => Reason v -> t v a
err reason = do
  span <- ask
  ctx <- askContext
  throwError $ Err span reason ctx

mismatch :: Has (Reader (Context (Val v ::: Type v)) :+: Reader Span :+: Throw (Err v)) sig (t v) => String -> Either String (Type v) -> Type v -> t v a
mismatch msg exp act = err $ Mismatch msg exp act

couldNotUnify :: Has (Reader (Context (Val v ::: Type v)) :+: Reader Span :+: Throw (Err v)) sig (t v) => Type v -> Type v -> t v a
couldNotUnify t1 t2 = mismatch "mismatch" (Right t2) t1

couldNotSynthesize :: String -> Elab v a
couldNotSynthesize = err . CouldNotSynthesize

freeVariable :: DName -> Elab v a
freeVariable = err . FreeVariable

expectChecked :: Maybe (Type v) -> String -> Elab v (Type v)
expectChecked t msg = maybe (couldNotSynthesize msg) pure t


-- Patterns

expectMatch :: (Type v -> Maybe out) -> String -> String -> Type v -> Elab v out
expectMatch pat exp s _T = maybe (mismatch s (Left exp) _T) pure (pat _T)

expectQuantifiedType :: String -> Type v -> Elab v (Pl_ UName ::: Type v, Type v -> Type v)
expectQuantifiedType = expectMatch unForAll "{_} -> _"

expectProductType :: String -> Type v -> Elab v (Type v, Type v)
expectProductType = expectMatch unProductT "(_, _)"
