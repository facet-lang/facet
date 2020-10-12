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
( ErrM(..)
, Context
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
, showContext
) where

import           Control.Algebra
import           Control.Applicative (liftA2)
import           Control.Carrier.Error.Church
import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Effect.Parser.Span (Span(..))
import           Control.Effect.Sum
import           Data.Bifunctor (first)
import           Data.Foldable (foldl', toList)
import           Data.List (intersperse)
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Semigroup (stimes)
import qualified Data.Text as T
import           Data.Traversable (for)
import           Facet.Context
import qualified Facet.Core.Module as CM
import qualified Facet.Core.Pattern as CP
import           Facet.Core.Value hiding (bound, global, ($$))
import qualified Facet.Core.Value as CV
import qualified Facet.Env as Env
import           Facet.Error
import           Facet.Name (Index(..), Level(..), QName(..), UName, indexToLevel)
import qualified Facet.Name as N
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
import           Silkscreen (colon, fillSep, flatAlt, group, line, nest, pretty, softline, space, (</>))
import           Text.Parser.Position (Spanned)

type Type = Value ErrM Level
type Expr = Value ErrM Level

newtype ErrM a = ErrM { rethrow :: forall sig m . Has (Throw Err) sig m => m a }

instance Functor ErrM where
  fmap f (ErrM m) = ErrM (fmap f m)

instance Applicative ErrM where
  pure a = ErrM $ pure a
  ErrM f <*> ErrM a = ErrM (f <*> a)

instance Monad ErrM where
  ErrM m >>= f = ErrM $ m >>= rethrow . f

instance Algebra (Throw Err) ErrM where
  alg hdl sig ctx = ErrM $ alg (rethrow . hdl) (inj sig) ctx


newtype Elab a = Elab { elab :: forall sig m . Has (Reader (Env.Env ErrM) :+: Reader (Context Type) :+: Reader Span :+: Throw Err) sig m => m a }

instance Functor Elab where
  fmap f (Elab m) = Elab (fmap f m)

instance Applicative Elab where
  pure a = Elab $ pure a
  Elab f <*> Elab a = Elab (f <*> a)

instance Monad Elab where
  Elab m >>= f = Elab $ m >>= elab . f

instance Algebra (Reader (Env.Env ErrM) :+: Reader (Context Type) :+: Reader Span :+: Throw Err) Elab where
  alg hdl sig ctx = case sig of
    L renv -> Elab $ alg (elab . hdl) (inj renv) ctx
    R (L rctx) -> Elab $ alg (elab . hdl) (inj rctx) ctx
    R (R (L rspan)) -> Elab $ alg (elab . hdl) (inj rspan) ctx
    R (R (R throw)) -> Elab $ alg (elab . hdl) (inj throw) ctx


newtype Check a = Check { runCheck :: Type -> Elab a }
  deriving (Algebra (Reader Type :+: Reader (Env.Env ErrM) :+: Reader (Context Type) :+: Reader Span :+: Throw Err), Applicative, Functor, Monad) via ReaderC Type Elab

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
  :: HasCallStack
  => Type
  -> Type
  -> Elab Type
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


-- General

switch
  :: HasCallStack
  => Synth a
  -> Maybe Type
  -> Elab (a ::: Type)
switch (Synth m) = \case
  Just _K -> m >>= \ (a ::: _K') -> (a :::) <$> unify _K' _K
  _       -> m

global
  :: N.DName
  -> Synth (Value ErrM Level)
global n = Synth $ asks (Env.lookup n) >>= \case
  Just b  -> do
    ctx <- ask @(Context Type)
    pure (CV.global (tm b :.: n) ::: shift (Level (length ctx)) (ty b))
  Nothing -> freeVariable (pretty n)

bound
  :: Index
  -> Synth (Value ErrM Level)
bound n = Synth $ do
  ctx <- ask @(Context Type)
  let level = indexToLevel (length ctx) n
  case ctx !? n of
    Just (_ ::: _T) -> pure (CV.bound level ::: _T)
    Nothing         -> err $ fillSep [ reflow "no variable bound for index", pretty (getIndex n), reflow "in context of length", pretty (length ctx) ]

hole
  :: HasCallStack
  => T.Text
  -> Check a
hole n = Check $ \ _T -> do
  _T' <- printType _T
  err $ fillSep [reflow "found hole", pretty n, colon, _T' ]

($$)
  :: Synth (Value ErrM Level)
  -> Check (Value ErrM Level)
  -> Synth (Value ErrM Level)
f $$ a = Synth $ do
  f' ::: _F <- synth f
  (_A, _B) <- expectFunctionType (pretty "in application") _F
  a' <- check (a ::: _A)
  (::: _B) <$> rethrow (f' CV.$$ a')


(|-)
  :: Has (Reader (Context Type) :+: Reader (Env.Env ErrM) :+: Reader Span) sig m
  => UName ::: Type
  -> (a -> Elab b)
  -> m (a -> ErrM b)
t |- f = do
  span <- ask @Span
  ctx <- ask
  env <- ask @(Env.Env ErrM)
  pure $ runReader span . runReader (ctx |> t) . runReader env . elab . f

infix 1 |-

(|-*)
  :: Has (Reader (Context Type) :+: Reader (Env.Env ErrM) :+: Reader Span) sig m
  => CP.Pattern (UName ::: Type)
  -> (CP.Pattern a -> Elab b)
  -> m (CP.Pattern a -> ErrM b)
p |-* f = do
  span <- ask @Span
  ctx <- ask
  env <- ask @(Env.Env ErrM)
  pure $ runReader span . runReader (foldl' (|>) ctx p) . runReader env . elab . f

infix 1 |-*


-- Types

elabType
  :: HasCallStack
  => Spanned (ST.Type Spanned a)
  -> Maybe Type
  -> Elab (Type ::: Type)
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


_Type :: Synth Type
_Type = Synth $ pure $ Type ::: Type

_Void :: Synth Type
_Void = Synth $ pure $ Void ::: Type

_Unit :: Synth Type
_Unit = Synth $ pure $ Unit ::: Type

(.*)
  :: Check Type
  -> Check Type
  -> Synth Type
a .* b = Synth $ do
  a' <- check (a ::: Type)
  b' <- check (b ::: Type)
  pure $ (TPrd a' b') ::: Type

infixl 7 .*

(-->)
  :: Check Type
  -> Check Type
  -> Synth Type
a --> b = Synth $ do
  a' <- check (a ::: Type)
  b' <- check (b ::: Type)
  pure $ (a' :-> b') ::: Type

infixr 2 -->

(>~>)
  :: (UName ::: Check Type)
  -> Check Type
  -> Synth Type
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
  -> Maybe Type
  -> Elab (Expr ::: Type)
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
  -> Check Expr
  -> Check Expr
tlam n b = Check $ \ ty -> do
  (_ ::: _T, _B) <- expectQuantifiedType (reflow "when checking type lambda") ty
  b' <- n ::: _T |- \ v -> do
    _B' <- rethrow (_B v)
    check (b ::: _B')
  pure (TLam n b')

lam
  :: UName
  -> Check Expr
  -> Check Expr
lam n b = Check $ \ _T -> do
  (_A, _B) <- expectFunctionType (reflow "when checking lambda") _T
  -- FIXME: shouldn’t we use the bound variable?
  b' <- n ::: _A |- \ v -> check (b ::: _B)
  pure (Lam [(CP.Var n, b')])

unit :: Synth Expr
unit = Synth . pure $ Unit ::: TUnit

(**)
  :: Check Expr
  -> Check Expr
  -> Check Expr
l ** r = Check $ \ _T -> do
  (_L, _R) <- expectProductType (reflow "when checking product") _T
  l' <- check (l ::: _L)
  r' <- check (r ::: _R)
  pure (Prd l' r')

comp
  :: Spanned (SE.Comp Spanned a)
  -> Check Expr
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
  -> Check (CP.Pattern (UName ::: Type))
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
  -> Check Expr ::: Check Type
elabDecl = withSpans $ \case
  (n ::: t) SD.:=> b ->
    let b' ::: _B = elabDecl b
    in tlam n b' ::: checkElab (switch (n ::: checkElab (elabType t) >~> _B))

  (n ::: t) SD.:-> b ->
    let b' ::: _B = elabDecl b
    -- FIXME: types and terms are bound with the same context, so the indices in the type are incremented, but arrow types don’t extend the context, so we were mishandling them.
    in lam n b' ::: checkElab (switch (checkElab (elabType t) --> local (|> (n ::: (Type :: Type))) _B))

  t SD.:= b ->
    checkElab (elabExpr b) ::: checkElab (elabType t)
  where
  withSpans f (s, d) = let t ::: _T = f d in setSpan s t ::: setSpan s _T


-- Modules

elabModule
  :: (HasCallStack, Has (Throw Err) sig m)
  => Spanned (SM.Module Spanned a)
  -> m (CM.Module ErrM Level)
elabModule (s, (SM.Module mname ds)) = runReader s . evalState (mempty @(Env.Env ErrM)) $ do
  -- FIXME: elaborate all the types first, and only then the terms
  -- FIXME: maybe figure out the graph for mutual recursion?
  defs <- for ds $ \ (s, (n, d)) -> setSpan s $ do
    env <- get @(Env.Env ErrM)
    e' ::: _T <- runReader @(Context Type) empty . runReader env $ do
      let e ::: t = elabDecl d
      _T <- elab $ check (t ::: Type)
      e' <- elab $ check (e ::: _T)
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

printTypeInContext :: (HasCallStack, Has (Reader (Context Type) :+: Reader Span :+: Throw Err) sig m) => Context P.Print -> Type -> m ErrDoc
printTypeInContext ctx = fmap P.getPrint . rethrow . foldContext P.printBinding P.printCoreValue ctx

showContext :: Has (Reader (Context Type) :+: Reader Span :+: Throw Err) sig m => m String
showContext = do
  ctx <- asks @(Context Type) elems
  let go Nil     = pure Nil
      go (as:>a) = do
        as' <- go as
        b'  <- showsPrecValue (Level (length as')) 0 (ty a)
        pure $ as' :> (tm a ::: b')
  shown <- rethrow $ go ctx
  pure $ showChar '[' . foldr (.) id (intersperse (showString ", ") (map (\ (t ::: _T) -> shows t {-. showString " : " . _T-}) (toList shown))) $ "]"

printContext :: (HasCallStack, Has (Reader (Context Type) :+: Reader Span :+: Throw Err) sig m) => m (Context P.Print)
printContext = do
  ctx <- ask @(Context Type)
  rethrow $ foldContextAll P.printBinding P.printCoreValue ctx

printType :: (HasCallStack, Has (Reader (Context Type) :+: Reader Span :+: Throw Err) sig m) => Type -> m ErrDoc
-- FIXME: this is still resulting in out of bounds printing
printType t = do
  ctx <- printContext
  printTypeInContext ctx t

err :: (HasCallStack, Has (Reader (Context Type) :+: Reader Span :+: Throw Err) sig m) => ErrDoc -> m a
err reason = do
  span <- ask
  ctx <- printContext
  throwError $ Err span (group reason) (zipWith (\ i -> P.getPrint . P.printContextEntry (Level i)) [0..] (toList (elems ctx)))

mismatch :: (HasCallStack, Has (Reader (Context Type) :+: Reader Span :+: Throw Err) sig m) => ErrDoc -> ErrDoc -> ErrDoc -> m a
mismatch msg exp act = err $ msg
  </> pretty "expected:" <> print exp
  </> pretty "  actual:" <> print act
  where
  -- line things up nicely for e.g. wrapped function types
  print = nest 2 . (flatAlt (line <> stimes (3 :: Int) space) mempty <>)

couldNotUnify :: (HasCallStack, Has (Reader (Context Type) :+: Reader Span :+: Throw Err) sig m) => Type -> Type -> m a
couldNotUnify t1 t2 = do
  ctx <- printContext
  t1' <- printTypeInContext ctx t1
  t2' <- printTypeInContext ctx t2
  mismatch (reflow "mismatch") t2' t1'

couldNotSynthesize :: (HasCallStack, Has (Reader (Context Type) :+: Reader Span :+: Throw Err) sig m) => ErrDoc -> m a
couldNotSynthesize msg = err $ reflow "could not synthesize a type for" <> softline <> msg

freeVariable :: (HasCallStack, Has (Reader (Context Type) :+: Reader Span :+: Throw Err) sig m) => ErrDoc -> m a
freeVariable v = err $ fillSep [reflow "variable not in scope:", v]

expectChecked :: (HasCallStack, Has (Reader (Context Type) :+: Reader Span :+: Throw Err) sig m) => Maybe Type -> ErrDoc -> m Type
expectChecked t msg = maybe (couldNotSynthesize msg) pure t


-- Patterns

expectMatch :: (HasCallStack, Has (Reader (Context Type) :+: Reader Span :+: Throw Err) sig m) => (Type -> Maybe out) -> ErrDoc -> ErrDoc -> Type -> m out
expectMatch pat exp s _T = do
  _T' <- printType _T
  maybe (mismatch s exp _T') pure (pat _T)

expectQuantifiedType :: (HasCallStack, Has (Reader (Context Type) :+: Reader Span :+: Throw Err) sig m) => ErrDoc -> Type -> m (UName ::: Type, Type -> ErrM Type)
expectQuantifiedType = expectMatch unForAll (pretty "{_} -> _")

expectFunctionType :: (HasCallStack, Has (Reader (Context Type) :+: Reader Span :+: Throw Err) sig m) => ErrDoc -> Type -> m (Type, Type)
expectFunctionType = expectMatch unArrow (pretty "_ -> _")

expectProductType :: (HasCallStack, Has (Reader (Context Type) :+: Reader Span :+: Throw Err) sig m) => ErrDoc -> Type -> m (Type, Type)
expectProductType = expectMatch unProductT (pretty "(_, _)")
