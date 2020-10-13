{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Elab
( M(..)
, Context
, Val
, Type
, Expr
, Elab(..)
, Check(..)
, Synth(..)
, check
, unify
, Metacontext(..)
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
, Err(..)
, Reason(..)
, printReason
) where

import           Control.Algebra
import           Control.Applicative (liftA2)
import           Control.Carrier.Error.Church
import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Effect.Parser.Span (Span(..))
import           Control.Effect.Sum
import           Control.Monad ((<=<))
import           Data.Bifunctor (first)
import           Data.Foldable (foldl', toList)
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Semigroup (stimes)
import qualified Data.Text as T
import           Data.Traversable (for)
import           Facet.Context hiding (getMetacontext)
import qualified Facet.Core.Module as CM
import qualified Facet.Core.Pattern as CP
import           Facet.Core.Value hiding (bound, global, ($$))
import qualified Facet.Core.Value as CV
import qualified Facet.Env as Env
import           Facet.Name (DName, Index(..), Level(..), QName(..), UName, indexToLevel)
import           Facet.Pretty (reflow)
import qualified Facet.Print as P
import           Facet.Stack hiding ((!?))
import qualified Facet.Surface.Decl as SD
import qualified Facet.Surface.Expr as SE
import qualified Facet.Surface.Module as SM
import qualified Facet.Surface.Pattern as SP
import qualified Facet.Surface.Type as ST
import           Facet.Syntax
import           GHC.Stack
import           Prelude hiding ((**))
import           Prettyprinter (Doc)
import           Prettyprinter.Render.Terminal (AnsiStyle)
import           Silkscreen (colon, fillSep, flatAlt, group, line, nest, pretty, softline, space, (</>))
import           Text.Parser.Position (Spanned)

type Val v = Value (M v) v
type Type v = Value (M v) v
type Expr v = Value (M v) v

newtype M v a = M { rethrow :: forall sig m . Has (State (Metacontext (Val v ::: Type v)) :+: Throw Err) sig m => m a }

instance Functor (M v) where
  fmap f (M m) = M (fmap f m)

instance Applicative (M v) where
  pure a = M $ pure a
  M f <*> M a = M (f <*> a)

instance Monad (M v) where
  M m >>= f = M $ m >>= rethrow . f

instance Algebra (State (Metacontext (Val v ::: Type v)) :+: Throw Err) (M v) where
  alg hdl sig ctx = case sig of
    L smctx -> M $ alg (rethrow . hdl) (inj smctx) ctx
    R throw -> M $ alg (rethrow . hdl) (inj throw) ctx


newtype Elab v a = Elab { elab :: forall sig m . Has (Reader (Env.Env (Type v)) :+: Reader (Context (Val v ::: Type v)) :+: Reader Span :+: State (Metacontext (Val v ::: Type v)) :+: Throw Err) sig m => m a }

instance Functor (Elab v) where
  fmap f (Elab m) = Elab (fmap f m)

instance Applicative (Elab v) where
  pure a = Elab $ pure a
  Elab f <*> Elab a = Elab (f <*> a)

instance Monad (Elab v) where
  Elab m >>= f = Elab $ m >>= elab . f

instance Algebra (Reader (Env.Env (Type v)) :+: Reader (Context (Val v ::: Type v)) :+: Reader Span :+: State (Metacontext (Val v ::: Type v)) :+: Throw Err) (Elab v) where
  alg hdl sig ctx = case sig of
    L renv              -> Elab $ alg (elab . hdl) (inj renv) ctx
    R (L rctx)          -> Elab $ alg (elab . hdl) (inj rctx) ctx
    R (R (L rspan))     -> Elab $ alg (elab . hdl) (inj rspan) ctx
    R (R (R (L smctx))) -> Elab $ alg (elab . hdl) (inj smctx) ctx
    R (R (R (R throw))) -> Elab $ alg (elab . hdl) (inj throw) ctx

askEnv :: Elab v (Env.Env (Type v))
askEnv = ask

askContext :: Elab v (Context (Val v ::: Type v))
askContext = ask

getMetacontext :: Elab v (Metacontext (Val v ::: Type v))
getMetacontext = get



newtype Check v a = Check { runCheck :: Type v -> Elab v a }
  deriving (Algebra (Reader (Type v) :+: Reader (Env.Env (Type v)) :+: Reader (Context (Val v ::: Type v)) :+: Reader Span :+: State (Metacontext (Val v ::: Type v)) :+: Throw Err), Applicative, Functor, Monad) via ReaderC (Type v) (Elab v)

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
  :: HasCallStack
  => Type Level
  -> Type Level
  -> Elab Level (Type Level)
unify t1 t2 = go t1 t2
  where
  go t1 t2 = case (t1, t2) of
    -- FIXME: this is missing a lot of cases
    (Type,       Type)       -> pure Type
    (Void,       Void)       -> pure Void
    (TUnit,      TUnit)      -> pure TUnit
    (Unit,       Unit)       -> pure Unit
    -- FIXME: resolve globals to try to progress past certain inequalities
    (f1 :$ a1,   f2 :$ a2)
      | f1 == f2
      , Just a <- goS a1 a2 -> (f1 :$) <$> a
    (a1 :-> b1,  a2 :-> b2)  -> (:->) <$> go a1 a2 <*> go b1 b2
    (t1 :=> b1,  t2 :=> b2)  -> do
      t <- go (ty t1) (ty t2)
      b <- tm t1 ::: t |- \ v -> do
        b1' <- rethrow $ b1 v
        b2' <- rethrow $ b2 v
        go b1' b2'
      pure $ tm t1 ::: t :=> b
    (TPrd l1 r1, TPrd l2 r2) -> TPrd <$> go l1 l2 <*> go r1 r2
    (Prd  l1 r1, Prd  l2 r2) -> Prd  <$> go l1 l2 <*> go r1 r2
    -- FIXME: build and display a diff of the root types
    _                       -> couldNotUnify t1 t2

  goS Nil        Nil        = Just (pure Nil)
  goS (i1 :> l1) (i2 :> l2) = liftA2 (:>) <$> goS i1 i2 <*> Just (go l1 l2)
  goS _          _          = Nothing


-- FIXME: is it possible to do something clever with delimited continuations or coroutines to bind variables outside our scope?


meta :: UName ::: Val Level ::: Type Level -> Elab Level (Type Level)
meta t = do
  mctx <- getMetacontext
  put (t <| mctx)
  pure $ CV.bound (metalevel mctx)


-- General

switch
  :: HasCallStack
  => Synth Level a
  -> Maybe (Type Level)
  -> Elab Level (a ::: Type Level)
switch (Synth m) = \case
  Just _K -> m >>= \ (a ::: _K') -> (a :::) <$> unify _K' _K
  _       -> m

global
  :: DName
  -> Synth Level (Val Level)
global n = Synth $ Env.lookup n <$> askEnv >>= \case
  Just b  -> do
    ctx <- askContext
    pure (CV.global (tm b :.: n) ::: shift (level ctx) (ty b))
  Nothing -> freeVariable n

bound
  :: Index
  -> Synth Level (Val Level)
bound n = Synth $ do
  ctx <- askContext
  let level = indexToLevel (length ctx) n
  case ctx !? n of
    Just (_ ::: (_ ::: _T)) -> pure (CV.bound level ::: _T)
    Nothing                 -> err $ fillSep [ reflow "no variable bound for index", pretty (getIndex n), reflow "in context of length", pretty (length ctx) ]

hole
  :: HasCallStack
  => T.Text
  -> Check Level a
hole n = Check $ \ _T -> do
  _T' <- printType _T
  err $ fillSep [reflow "found hole", pretty n, colon, _T' ]

($$)
  :: Synth Level (Val Level)
  -> Check Level (Val Level)
  -> Synth Level (Val Level)
f $$ a = Synth $ do
  f' ::: _F <- synth f
  (_A, _B) <- expectFunctionType (pretty "in application") _F
  a' <- check (a ::: _A)
  (::: _B) <$> rethrow (f' CV.$$ a')


(|-)
  :: UName ::: Type Level
  -> (Val Level -> Elab Level b)
  -> Elab Level (Val Level -> M Level b)
n ::: _T |- f = do
  span <- ask @Span
  ctx <- ask
  env <- askEnv
  pure $ \ v -> runReader span (runReader (ctx |> (n ::: v ::: _T)) (runReader env (elab (f v))))

infix 1 |-

(|-*)
  :: CP.Pattern (UName ::: Type Level)
  -> (CP.Pattern (Val Level) -> Elab Level b)
  -> Elab Level (CP.Pattern (Val Level) -> M Level b)
p |-* f = do
  span <- ask @Span
  ctx <- askContext
  env <- askEnv
  pure $ \ v -> runReader span (runReader (foldl' (|>) ctx (zipWith (\ (n ::: _T) v -> n ::: v ::: _T) (toList p) (toList v))) (runReader env (elab (f v))))

infix 1 |-*


-- Types

elabType
  :: HasCallStack
  => Spanned (ST.Type Spanned a)
  -> Maybe (Type Level)
  -> Elab Level (Type Level ::: Type Level)
elabType = withSpan' $ \case
  ST.Free  n -> switch $ global n
  ST.Bound n -> switch $ bound n
  ST.Hole  n -> check (hole n) (pretty "hole")
  ST.Type    -> switch $ _Type
  ST.Void    -> switch $ _Void
  ST.Unit    -> switch $ _Unit
  t ST.:=> b -> switch $ fmap (checkElab . elabType) t >~> checkElab (elabType b)
  f ST.:$  a -> switch $ synthElab (elabType f) $$  checkElab (elabType a)
  a ST.:-> b -> switch $ checkElab (elabType a) --> checkElab (elabType b)
  l ST.:*  r -> switch $ checkElab (elabType l) .*  checkElab (elabType r)
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
a --> b = Synth $ do
  a' <- check (a ::: Type)
  b' <- check (b ::: Type)
  pure $ (a' :-> b') ::: Type

infixr 2 -->

(>~>)
  :: (UName ::: Check Level (Type Level))
  -> Check Level (Type Level)
  -> Synth Level (Type Level)
(n ::: t) >~> b = Synth $ do
  _T <- check (t ::: Type)
  -- FIXME: shouldn’t we use the bound variable?
  b' <- n ::: _T |- \ v -> check (b ::: Type)
  pure $ (n ::: _T :=> b') ::: Type

infixr 1 >~>


-- Expressions

elabExpr
  :: HasCallStack
  => Spanned (SE.Expr Spanned a)
  -> Maybe (Type Level)
  -> Elab Level (Expr Level ::: Type Level)
elabExpr = withSpan' $ \case
  SE.Free  n -> switch $ global n
  SE.Bound n -> switch $ bound n
  SE.Hole  n -> check (hole n) (pretty "hole")
  f SE.:$  a -> switch $ synthElab (elabExpr f) $$ checkElab (elabExpr a)
  l SE.:*  r -> check (checkElab (elabExpr l) ** checkElab (elabExpr r)) (pretty "product")
  SE.Unit    -> switch unit
  SE.Comp cs -> check (comp cs) (pretty "computation")
  where
  check m msg _T = expectChecked _T msg >>= \ _T -> (::: _T) <$> runCheck m _T


tlam
  :: UName
  -> Check Level (Expr Level)
  -> Check Level (Expr Level)
tlam n b = Check $ \ ty -> do
  (_ ::: _T, _B) <- expectQuantifiedType (reflow "when checking type lambda") ty
  b' <- n ::: _T |- \ v -> do
    _B' <- rethrow (_B v)
    check (b ::: _B')
  pure (TLam n b')

lam
  :: UName
  -> Check Level (Expr Level)
  -> Check Level (Expr Level)
lam n b = Check $ \ _T -> do
  (_A, _B) <- expectFunctionType (reflow "when checking lambda") _T
  -- FIXME: shouldn’t we use the bound variable?
  b' <- CP.Var (n ::: _A) |-* \ v -> check (b ::: _B)
  pure (Lam [(CP.Var n, b')])

unit :: Synth v (Expr v)
unit = Synth . pure $ Unit ::: TUnit

(**)
  :: Check Level (Expr Level)
  -> Check Level (Expr Level)
  -> Check Level (Expr Level)
l ** r = Check $ \ _T -> do
  (_L, _R) <- expectProductType (reflow "when checking product") _T
  l' <- check (l ::: _L)
  r' <- check (r ::: _R)
  pure (Prd l' r')

comp
  :: HasCallStack
  => Spanned (SE.Comp Spanned a)
  -> Check Level (Expr Level)
comp = withSpan $ \case
  SE.Expr    b  -> checkElab (elabExpr b)
  -- FIXME: this shape makes it hard to elaborate nested pattern matches, because we kind of need to transpose the table.
  -- e.g. in xor : Bool -> Bool -> Bool { False True -> True, True False -> True, _ _ -> False }, we should have the second column of cases appearing under each of the first, or else we’re inserting inexhaustive patterns
  SE.Clauses cs -> Check $ \ _T -> do
    (_A, _B) <- expectFunctionType (reflow "when checking clauses") _T
    Lam <$> case cs of
      [] -> [] <$ unify _A Void
      cs -> traverse (uncurry (clause _A _B)) cs
  where
  clause _A _B (p:|ps) b = do
    p' <- check (pattern p ::: _A)
    -- FIXME: shouldn’t we use the bound variable(s)?
    b' <- p' |-* \ v -> check (go ps b ::: _B)
    pure (tm <$> p', b')
  go []     b = checkElab (elabExpr b)
  go (p:ps) b = Check $ \ _T -> do
    (_A, _B) <- expectFunctionType (reflow "when checking clause") _T
    Lam <$> (pure <$> clause _A _B (p:|ps) b)


pattern
  :: Spanned (SP.Pattern Spanned UName)
  -> Check Level (CP.Pattern (UName ::: Type Level))
pattern = withSpan $ \case
  SP.Wildcard -> pure CP.Wildcard
  SP.Var n    -> Check $ \ _T -> pure (CP.Var (n ::: _T))
  SP.Tuple ps -> Check $ \ _T -> CP.Tuple . toList <$> go _T (fromList ps)
    where
    go _T = \case
      Nil      -> Nil      <$  unify TUnit _T
      Nil :> p -> (Nil :>) <$> check (pattern p ::: _T)
      ps  :> p -> do
        (_L, _R) <- expectProductType (reflow "when checking tuple pattern") _T
        (:>) <$> go _L ps <*> check (pattern p ::: _R)


-- Declarations

elabDecl
  :: HasCallStack
  => Spanned (SD.Decl Spanned a)
  -> Check Level (Expr Level) ::: Check Level (Type Level)
elabDecl = withSpans $ \case
  (n ::: t) SD.:=> b ->
    let b' ::: _B = elabDecl b
    in tlam n b' ::: checkElab (switch (n ::: checkElab (elabType t) >~> _B))

  (n ::: t) SD.:-> b ->
    let b' ::: _B = elabDecl b
    -- FIXME: types and terms are bound with the same context, so the indices in the type are incremented, but arrow types don’t extend the context, so we were mishandling them.
    in lam n b' ::: checkElab (switch (checkElab (elabType t) --> local (|> (n ::: (Type :: Type Level) ::: (Type :: Type Level))) _B))

  t SD.:= b ->
    checkElab (elabExpr b) ::: checkElab (elabType t)
  where
  withSpans f (s, d) = let t ::: _T = f d in setSpan s t ::: setSpan s _T


-- Modules

elabModule
  :: (HasCallStack, Has (Throw Err) sig m)
  => Spanned (SM.Module Spanned a)
  -> m (CM.Module (M Level) Level)
elabModule (s, (SM.Module mname ds)) = runReader s . evalState (mempty @(Env.Env (Type Level))) $ do
  -- FIXME: elaborate all the types first, and only then the terms
  -- FIXME: maybe figure out the graph for mutual recursion?
  defs <- for ds $ \ (s, (n, d)) -> setSpan s $ do
    env <- get @(Env.Env (Type Level))
    e' ::: _T <- runReader @(Context (Val Level ::: Type Level)) empty . runReader env $ do
      let e ::: t = elabDecl d
      _T <- runState (\ _ -> pure) (Metacontext @(Val Level ::: Type Level) []) $ elab $ check (t ::: Type)
      e' <- runState (\ _ -> pure) (Metacontext @(Val Level ::: Type Level) []) $ elab $ check (e ::: _T)
      pure $ e' ::: _T

    modify $ Env.insert (mname :.: n ::: _T)
    -- FIXME: extend the module
    -- FIXME: support defining types
    pure (mname :.: n, CM.DTerm e' ::: _T)

  pure $ CM.Module mname defs


-- Errors

setSpan :: Has (Reader Span) sig m => Span -> m a -> m a
setSpan = local . const

withSpan :: Has (Reader Span) sig m => (a -> m b) -> (Span, a) -> m b
withSpan k (s, a) = setSpan s (k a)

withSpan' :: Has (Reader Span) sig m => (a -> b -> m c) -> (Span, a) -> b -> m c
withSpan' k (s, a) b = setSpan s (k a b)


type ErrDoc = Doc AnsiStyle

data Err = Err
  { span    :: Span
  , reason  :: ErrDoc
  , context :: [ErrDoc]
  }
  deriving (Show)

data Reason
  = FreeVariable DName
  | CouldNotSynthesize ErrDoc
  | Mismatch ErrDoc ErrDoc ErrDoc
  | Hole T.Text ErrDoc
  | BadContext Index Level
  deriving (Show)

printReason :: Reason -> ErrDoc
printReason = \case
  FreeVariable n         -> fillSep [reflow "variable not in scope:", pretty n]
  CouldNotSynthesize msg -> reflow "could not synthesize a type for" <> softline <> msg
  Mismatch msg exp act   -> msg
    </> pretty "expected:" <> print exp
    </> pretty "  actual:" <> print act
    where
    -- line things up nicely for e.g. wrapped function types
    print = nest 2 . (flatAlt (line <> stimes (3 :: Int) space) mempty <>)
  Hole n _T              -> fillSep [reflow "found hole", pretty n, colon, _T ]
  BadContext n l         -> fillSep [ reflow "no variable bound for index", pretty (getIndex n), reflow "in context of length", pretty (getLevel l) ]


printTypeInContext :: HasCallStack => [Value (M Level) P.Print] -> Stack (Value (M Level) P.Print) -> Type Level -> Elab Level ErrDoc
printTypeInContext mctx ctx = fmap P.getPrint . rethrow . (P.printCoreValue (Level 0) <=< rethrow . mapValue mctx ctx)

printContext :: HasCallStack => Elab Level ([Value (M Level) P.Print], Stack (Value (M Level) P.Print))
printContext = do
  Metacontext mctx <- getMetacontext
  Context ctx <- askContext
  -- FIXME: This prints the wrong thing w.r.t. showing the types in error messages; e.g. it shows an expected type of Type -> (Type -> Type) -> Type when it should show the names A0/B1.
  rethrow $ mapValueAll (ty . ty <$> mctx) (ty . ty <$> ctx)

printType :: HasCallStack => Type Level -> Elab Level ErrDoc
printType t = do
  (mctx, ctx) <- printContext
  printTypeInContext mctx ctx t

err :: HasCallStack => ErrDoc -> Elab Level a
err reason = do
  span <- ask
  ctx <- askContext
  (mctx, ctx') <- printContext
  ctx' <- rethrow $ traverse (P.printCoreValue (level ctx)) ctx'
  -- FIXME: show the metacontext
  -- FIXME: show the types as well as the names
  throwError $ Err span (group reason) (zipWith3 (\ i n -> P.getPrint . P.printContextEntry (Level i) . (n :::)) [0..] (toList (names ctx)) (toList ctx'))

mismatch :: HasCallStack => ErrDoc -> ErrDoc -> ErrDoc -> Elab Level a
mismatch msg exp act = err $ msg
  </> pretty "expected:" <> print exp
  </> pretty "  actual:" <> print act
  where
  -- line things up nicely for e.g. wrapped function types
  print = nest 2 . (flatAlt (line <> stimes (3 :: Int) space) mempty <>)

couldNotUnify :: HasCallStack => Type Level -> Type Level -> Elab Level a
couldNotUnify t1 t2 = do
  (mctx, ctx) <- printContext
  t1' <- printTypeInContext mctx ctx t1
  t2' <- printTypeInContext mctx ctx t2
  mismatch (reflow "mismatch") t2' t1'

couldNotSynthesize :: HasCallStack => ErrDoc -> Elab Level a
couldNotSynthesize msg = err $ reflow "could not synthesize a type for" <> softline <> msg

freeVariable :: HasCallStack => DName -> Elab Level a
freeVariable v = err $ fillSep [reflow "variable not in scope:", pretty v]

expectChecked :: HasCallStack => Maybe (Type Level) -> ErrDoc -> Elab Level (Type Level)
expectChecked t msg = maybe (couldNotSynthesize msg) pure t


-- Patterns

expectMatch :: HasCallStack => (Type Level -> Maybe out) -> ErrDoc -> ErrDoc -> Type Level -> Elab Level out
expectMatch pat exp s _T = do
  _T' <- printType _T
  maybe (mismatch s exp _T') pure (pat _T)

expectQuantifiedType :: HasCallStack => ErrDoc -> Type Level -> Elab Level (UName ::: Type Level, Type Level -> M Level (Type Level))
expectQuantifiedType = expectMatch unForAll (pretty "{_} -> _")

expectFunctionType :: HasCallStack => ErrDoc -> Type Level -> Elab Level (Type Level, Type Level)
expectFunctionType = expectMatch unArrow (pretty "_ -> _")

expectProductType :: HasCallStack => ErrDoc -> Type Level -> Elab Level (Type Level, Type Level)
expectProductType = expectMatch unProductT (pretty "(_, _)")
