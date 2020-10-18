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
( Type
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
, (-->)
, (>~>)
  -- * Expressions
, elabExpr
, ($$)
, tlam
, lam
  -- * Declarations
, elabDecl
  -- * Modules
, elabModule
  -- * Errors
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
import           Text.Parser.Position (Spanned)

type Type = Value
type Expr = Value
type Prob = Value

type Subst = IntMap.IntMap (Maybe Prob ::: Type)

newtype Elab a = Elab { elab :: forall sig m . Has (Reader (Env.Env Type) :+: Reader (Context (Value ::: Type)) :+: Reader Span :+: State Subst :+: Throw Err) sig m => m a }

instance Functor Elab where
  fmap f (Elab m) = Elab (fmap f m)

instance Applicative Elab where
  pure a = Elab $ pure a
  Elab f <*> Elab a = Elab (f <*> a)

instance Monad Elab where
  Elab m >>= f = Elab $ m >>= elab . f

instance Algebra (Reader (Env.Env Type) :+: Reader (Context (Value ::: Type)) :+: Reader Span :+: State Subst :+: Throw Err) Elab where
  alg hdl sig ctx = case sig of
    L renv              -> Elab $ alg (elab . hdl) (inj renv) ctx
    R (L rctx)          -> Elab $ alg (elab . hdl) (inj rctx) ctx
    R (R (L rspan))     -> Elab $ alg (elab . hdl) (inj rspan) ctx
    R (R (R (L smctx))) -> Elab $ alg (elab . hdl) (inj smctx) ctx
    R (R (R (R throw))) -> Elab $ alg (elab . hdl) (inj throw) ctx


askEnv :: Has (Reader (Env.Env Type)) sig m => m (Env.Env Type)
askEnv = ask

askContext :: Has (Reader (Context (Value ::: Type))) sig m => m (Context (Value ::: Type))
askContext = ask


newtype Check a = Check { runCheck :: Type -> Elab a }
  deriving (Algebra (Reader Type :+: Reader (Env.Env Type) :+: Reader (Context (Value ::: Type)) :+: Reader Span :+: State Subst :+: Throw Err), Applicative, Functor, Monad) via ReaderC Type Elab

newtype Synth a = Synth { synth :: Elab (a ::: Type) }

instance Functor Synth where
  fmap f (Synth m) = Synth (first f <$> m)

check :: (Check a ::: Type) -> Elab a
check = uncurryAnn runCheck


checkElab :: (Maybe Type -> Elab (a ::: Type)) -> Check a
checkElab f = tm <$> Check (f . Just)

synthElab :: (Maybe Type -> Elab (a ::: Type)) -> Synth a
synthElab f = Synth (f Nothing)


unify
  :: Type :===: Type
  -> Elab Type
unify (t1 :===: t2) = go (t1 :===: t2)
  where
  go
    :: Prob :===: Prob
    -> Elab Type
  go = \case
    -- FIXME: this is missing a lot of cases
    Type                 :===: Type                 -> pure Type
    -- FIXME: resolve globals to try to progress past certain inequalities
    Neut h1 e1           :===: Neut h2 e2
      | h1 == h2
      , Just e' <- unifyS (e1 :===: e2) -> Neut h1 <$> e'
    Neut (Metavar v) Nil :===: x                    -> solve (tm v :=: x)
    x                    :===: Neut (Metavar v) Nil -> solve (tm v :=: x)
    t1 :=> b1            :===: t2 :=> b2
      | pl (tm t1) == pl (tm t2) -> do
        t <- go (ty t1 :===: ty t2)
        b <- out (tm t1) ::: t |- \ v ->
          go (b1 v :===: b2 v)
        pure $ tm t1 ::: t :=> b
    -- FIXME: build and display a diff of the root types
    t1                   :===: t2                   -> couldNotUnify t1 t2

  unifyS (Nil          :===: Nil)          = Just (pure Nil)
  -- NB: we make no attempt to unify case eliminations because they shouldn’t appear in types anyway.
  unifyS (i1 :> App l1 :===: i2 :> App l2)
    | pl l1 == pl l2                       = liftA2 (:>) <$> unifyS (i1 :===: i2) <*> Just (App . P (pl l1) <$> go (out l1 :===: out l2))
  unifyS _                                 = Nothing

  solve :: Meta :=: Prob -> Elab Value
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
resolve n = Synth $ Env.lookup n <$> askEnv >>= \case
  Just (m :=: _ ::: _T) -> pure $ m :.: n ::: _T
  Nothing
    | E (EName n) <- n  -> synth (resolve (C (CName n)))
    | otherwise         -> freeVariable n

global
  :: DName
  -> Synth Value
global n = Synth $ do
  q <- synth (resolve n)
  instantiate (C.global q ::: ty q)

bound
  :: Context (Value ::: Type)
  -> Index
  -> Synth Value
bound ctx n = Synth $ case ctx !? n of
  -- FIXME: do we need to instantiate here to deal with rank-n applications?
  Just (_ ::: (v ::: _T)) -> pure (v ::: _T)
  Nothing                 -> err $ BadContext n

hole
  :: T.Text
  -> Check a
hole n = Check $ \ _T -> err $ Hole n _T

($$)
  :: Synth Value
  -> Check Value
  -> Synth Value
f $$ a = Synth $ do
  f' ::: _F <- synth f
  (_A, _B) <- expectQuantifiedType "in application" _F
  a' <- check (a ::: ty _A)
  pure $ (f' C.$$ ex a') ::: _B a'


(|-)
  :: UName ::: Type
  -> (Value -> Elab Value)
  -> Elab (Value -> Value)
n ::: _T |- f = do
  m <- meta _T
  handleBinder m (\ v -> local (|> (n ::: v ::: _T)) (f v))

infix 1 |-

(|-*)
  :: C.Pattern Type (UName ::: Type)
  -> (C.Pattern Type Value -> Elab Value)
  -> Elab (C.Pattern Type Value -> Value)
p |-* f = do
  mp <- traverse (meta . ty) p
  handleBinderP mp (\ v ->
    local (flip (foldl' (|>)) (zipWith (\ (n ::: _T) v -> n ::: v ::: _T) (toList p) (toList v))) (f v))

infix 1 |-*


-- Types

elabType
  :: HasCallStack
  => Context (Value ::: Type)
  -> Spanned S.Type
  -> Maybe Type
  -> Elab (Type ::: Type)
elabType ctx = withSpan' $ \case
  S.TFree  n -> switch $ global n
  S.TBound n -> switch $ bound ctx n
  S.THole  n -> check (hole n) "hole"
  S.Type     -> switch $ _Type
  t S.:=> b  -> switch $ bimap im (checkElab . elabType ctx) t >~> \ v -> checkElab (elabType (ctx |> v) b)
  f S.:$$ a  -> switch $ synthElab (elabType ctx f) $$  checkElab (elabType ctx a)
  a S.:-> b  -> switch $ checkElab (elabType ctx a) --> checkElab (elabType ctx b)
  where
  check m msg _T = expectChecked _T msg >>= \ _T -> (::: _T) <$> runCheck m _T


_Type :: Synth Type
_Type = Synth $ pure $ Type ::: Type

(-->)
  :: Check Type
  -> Check Type
  -> Synth Type
a --> b = ex __ ::: a >~> const b

infixr 1 -->

(>~>)
  :: (Pl_ UName ::: Check Type)
  -> (UName ::: Value ::: Type -> Check Type)
  -> Synth Type
(n ::: t) >~> b = Synth $ do
  _T <- check (t ::: Type)
  b' <- out n ::: _T |- \ v -> check (b (out n ::: v ::: _T) ::: Type)
  pure $ (n ::: _T :=> b') ::: Type

infixr 1 >~>


-- Expressions

elabExpr
  :: HasCallStack
  => Context (Value ::: Type)
  -> Spanned S.Expr
  -> Maybe Type
  -> Elab (Expr ::: Type)
elabExpr ctx = withSpan' $ \case
  S.Free  n -> switch $ global n
  S.Bound n -> switch $ bound ctx n
  S.Hole  n -> check (hole n) "hole"
  f S.:$  a -> switch $ synthElab (elabExpr ctx f) $$ checkElab (elabExpr ctx a)
  S.Comp cs -> check (elabComp ctx cs) "computation"
  where
  check m msg _T = expectChecked _T msg >>= \ _T -> (::: _T) <$> runCheck m _T


tlam
  :: UName
  -> (UName ::: Type ::: Type -> Check Expr)
  -> Check Expr
tlam n b = Check $ \ ty -> do
  (_ ::: _T, _B) <- expectQuantifiedType "when checking type lambda" ty
  b' <- n ::: _T |- \ v -> check (b (n ::: v ::: _T) ::: _B v)
  pure (Lam (im n ::: _T) b')

lam
  :: UName
  -> (UName ::: Expr ::: Type -> Check Expr)
  -> Check Expr
lam n b = Check $ \ _T -> do
  (_A, _B) <- expectQuantifiedType "when checking lambda" _T
  b' <- n ::: ty _A |- \ v -> check (b (n ::: v ::: ty _A) ::: _B v)
  pure (Lam (ex n ::: ty _A) b')

elabComp
  :: HasCallStack
  => Context (Value ::: Type)
  -> Spanned S.Comp
  -> Check Expr
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

elabClauses :: Context (Value ::: Type) -> [(NonEmpty (Spanned S.Pattern), Spanned S.Expr)] -> Check Expr
-- FIXME: do the same thing for wildcards
elabClauses ctx [((_, S.PVar n):|ps, b)] = Check $ \ _T -> do
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
  :: Spanned S.Pattern
  -> Check (C.Pattern Type (UName ::: Type))
elabPattern = withSpan $ \case
  S.PVar n    -> Check $ \ _T -> pure (C.PVar (n ::: _T))
  S.PCon n ps -> Check $ \ _T -> do
    q ::: _T' <- synth (resolve (C n))
    let go _T' = \case
          Nil   -> Nil <$ unify (_T' :===: _T)
          ps:>p -> do
            (_A, _B) <- expectQuantifiedType "when checking constructor pattern" _T'
            -- FIXME: there’s no way this is going to work, let alone a good idea
            v <- metavar <$> meta (ty _A)
            ps' <- go (_B v) ps
            p' <- check (elabPattern p ::: ty _A)
            pure $ ps' :> p'
    C.PCon . Con (q ::: _T') <$> go _T' (fromList ps)


-- Declarations

elabDecl
  :: HasCallStack
  => Spanned S.Decl
  -> (Context (Value ::: Type) -> Check (Either [CName ::: Type] Value)) ::: (Context (Value ::: Type) -> Check Type)
elabDecl d = go d id id
  where
  go
    :: Spanned S.Decl
    -> ((Context (Value ::: Type) -> Check Value) -> (Context (Value ::: Type) -> Check Value))
    -> ((Context (Value ::: Type) -> Check Value) -> (Context (Value ::: Type) -> Check Value))
    -> (Context (Value ::: Type) -> Check (Either [CName ::: Type] Value)) ::: (Context (Value ::: Type) -> Check Type)
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

elabDeclBody :: HasCallStack => ((Context (Value ::: Type) -> Check Value) -> (Context (Value ::: Type) -> Check Value)) -> Context (Value ::: Type) -> S.DeclBody -> Check (Either [CName ::: Type] Value)
elabDeclBody k ctx = \case
  S.DExpr b -> Right <$> k (checkElab . (`elabExpr` b)) ctx
  S.DType b -> Right <$> k (checkElab . (`elabType` b)) ctx
  S.DData c -> Left <$> elabData k ctx c


elabData :: ((Context (Value ::: Type) -> Check Value) -> (Context (Value ::: Type) -> Check Value)) -> Context (Value ::: Type) -> [Spanned (CName ::: Spanned S.Type)] -> Check [CName ::: Type]
-- FIXME: check that all constructors return the datatype.
elabData k ctx cs = for cs $ withSpan $ \ (n ::: t) -> (n :::) <$> k (checkElab . (`elabType` t)) ctx


-- Modules

elabModule
  :: forall m sig
  .  (HasCallStack, Has (Throw Err) sig m)
  => Spanned S.Module
  -> m C.Module
elabModule (s, S.Module mname ds) = runReader s . evalState (mempty @(Env.Env Type)) $ do
  -- FIXME: trace the defs as we elaborate them
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
                  _T        -> VCon (Con (mname :.: C n ::: _T) fs)
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
  emptySubst = IntMap.empty @(Maybe Prob ::: Type)

  runContext = runReader @(Context (Value ::: Type)) empty
  runSubst = runState (fmap pure . apply) emptySubst

  runEnv m = do
    env <- get @(Env.Env Type)
    runReader env m



-- Errors

setSpan :: Has (Reader Span) sig m => Span -> m a -> m a
setSpan = local . const

withSpan :: Has (Reader Span) sig m => (a -> m b) -> (Span, a) -> m b
withSpan k (s, a) = setSpan s (k a)

withSpan' :: Has (Reader Span) sig m => (a -> b -> m c) -> (Span, a) -> b -> m c
withSpan' k (s, a) b = setSpan s (k a b)


data Err = Err
  { span    :: Span
  , reason  :: Reason
  , context :: Context (Value ::: Type)
  }

data Reason
  = FreeVariable DName
  | CouldNotSynthesize String
  | Mismatch String (Either String Type) Type
  | Hole T.Text Type
  | BadContext Index


err :: Has (Reader (Context (Value ::: Type)) :+: Reader Span :+: Throw Err) sig m => Reason -> m a
err reason = do
  span <- ask
  ctx <- askContext
  throwError $ Err span reason ctx

mismatch :: Has (Reader (Context (Value ::: Type)) :+: Reader Span :+: Throw Err) sig m => String -> Either String Type -> Type -> m a
mismatch msg exp act = err $ Mismatch msg exp act

couldNotUnify :: Has (Reader (Context (Value ::: Type)) :+: Reader Span :+: Throw Err) sig m => Type -> Type -> m a
couldNotUnify t1 t2 = mismatch "mismatch" (Right t2) t1

couldNotSynthesize :: String -> Elab a
couldNotSynthesize = err . CouldNotSynthesize

freeVariable :: DName -> Elab a
freeVariable = err . FreeVariable

expectChecked :: Maybe Type -> String -> Elab Type
expectChecked t msg = maybe (couldNotSynthesize msg) pure t


-- Patterns

expectMatch :: (Type -> Maybe out) -> String -> String -> Type -> Elab out
expectMatch pat exp s _T = maybe (mismatch s (Left exp) _T) pure (pat _T)

expectQuantifiedType :: String -> Type -> Elab (Pl_ UName ::: Type, Type -> Type)
expectQuantifiedType = expectMatch unForAll "{_} -> _"
