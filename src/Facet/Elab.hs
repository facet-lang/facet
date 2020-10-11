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
( ErrM
, runErrM
, Context
, elab
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
) where

import           Control.Algebra
import           Control.Applicative (liftA2)
import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Effect.Lift
import           Control.Effect.Parser.Span (Span(..))
import           Control.Monad.Trans.Class
import           Data.Bifunctor (first)
import           Data.Foldable (toList)
import           Data.Functor.Identity
import           Data.Semigroup (stimes)
import qualified Data.Text as T
import           Data.Traversable (for)
import           Facet.Carrier.Error.Context
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
import           Facet.Stack
import qualified Facet.Surface.Comp as SC
import qualified Facet.Surface.Decl as SD
import qualified Facet.Surface.Expr as SE
import qualified Facet.Surface.Module as SM
import qualified Facet.Surface.Pattern as SP
import qualified Facet.Surface.Type as ST
import           Facet.Syntax
import           GHC.Stack
import           Prelude hiding ((**))
import           Silkscreen (colon, fillSep, flatAlt, group, line, nest, pretty, softline, space, (</>))

type ErrM = ErrorC Span Err Identity

runErrM :: Span -> ErrM a -> Either (Span, Err) a
runErrM s = run . runError (curry (Identity . Left)) (Identity . Right) s

type Context = Stack (Value ErrM Level ::: Type ErrM Level)

elab :: Has (Reader Context :+: Reader (Env.Env ErrM) :+: Reader Span :+: Throw Err) sig m => Elab a -> m a
elab m = do
  ctx <- ask
  env <- ask
  rethrow (runReader ctx (runReader env (runElab m)))

rethrow :: Has (Reader Span :+: Throw Err) sig m => ErrM a -> m a
rethrow m = do
  span <- ask
  run (runError (\ s e -> pure (setSpan s (throwError e))) (pure . pure) span m)

liftErr :: ErrM a -> Elab a
liftErr = Elab . lift . lift

-- FIXME: can we generalize this to a rank-n quantified action over any context providing these effects?
newtype Elab a = Elab { runElab :: ReaderC (Env.Env ErrM) (ReaderC Context (ErrorC Span Err Identity)) a }
  deriving (Algebra (Reader (Env.Env ErrM) :+: Reader Context :+: Error Err :+: Reader Span :+: Lift Identity), Applicative, Functor, Monad)


newtype Check a = Check { runCheck :: Type ErrM Level -> Elab a }
  deriving (Algebra (Reader (Type ErrM Level) :+: Reader (Env.Env ErrM) :+: Reader Context :+: Error Err :+: Reader Span :+: Lift Identity), Applicative, Functor, Monad) via ReaderC (Type ErrM Level) Elab

newtype Synth a = Synth { synth :: Elab (a ::: Type ErrM Level) }

instance Functor Synth where
  fmap f (Synth m) = Synth (first f <$> m)

check :: (Check a ::: Type ErrM Level) -> Elab a
check = uncurryAnn runCheck


unify
  :: Type ErrM Level
  -> Type ErrM Level
  -> Elab (Type ErrM Level)
unify t1 t2 = go t1 t2
  where
  go t1 t2 = case (t1, t2) of
    -- FIXME: this is missing a lot of cases
    (Type,       Type)       -> pure Type
    (Void,       Void)       -> pure Void
    (Unit,       Unit)       -> pure Unit
    -- FIXME: resolve globals to try to progress past certain inequalities
    (f1 :$ a1,   f2 :$ a2)
      | f1 == f2
      , Just a <- goS a1 a2 -> (f1 :$) <$> a
    (a1 :-> b1,  a2 :-> b2)  -> (:->) <$> go a1 a2 <*> go b1 b2
    (t1 :=> b1,  t2 :=> b2)  -> do
      t <- go (ty t1) (ty t2)
      b <- elabBinder $ \ v -> v ::: t |- do
        b1' <- liftErr $ b1 v
        b2' <- liftErr $ b2 v
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
  :: Synth a
  -> Maybe (Type ErrM Level)
  -> Elab (a ::: Type ErrM Level)
switch (Synth m) = \case
  Just _K -> m >>= \ (a ::: _K') -> (a :::) <$> unify _K' _K
  _       -> m

global
  :: N.DName
  -> Synth QName
global n = Synth $ asks (Env.lookup n) >>= \case
  Just b  -> do
    ctx <- ask @Context
    pure (tm b :.: n ::: shift (Level (length ctx)) (ty b))
  Nothing -> freeVariable (pretty n)

bound
  :: Index
  -> Synth Level
bound n = Synth $ do
  ctx <- ask @Context
  let level = indexToLevel (length ctx) n
  case ctx !? getIndex n of
    Just (_ ::: _T) -> pure (level ::: _T)
    Nothing         -> err $ fillSep [ reflow "no variable bound for index", pretty (getIndex n), reflow "in context of length", pretty (length ctx) ]

($$)
  :: Synth (Value ErrM Level)
  -> Check (Value ErrM Level)
  -> Synth (Value ErrM Level)
f $$ a = Synth $ do
  f' ::: _F <- synth f
  (_A, _B) <- expectFunctionType (pretty "in application") _F
  a' <- check (a ::: _A)
  (::: _B) <$> liftErr (f' CV.$$ a')


elabBinder :: Has (Reader (Env.Env ErrM) :+: Reader Context) sig m => (a -> Elab b) -> m (a -> ErrM b)
elabBinder f = do
  env <- ask
  ctx <- ask
  pure $ \ a -> runReader ctx (runReader env (runElab (f a)))


-- Types

elabType
  :: ST.Type Span
  -> Maybe (Type ErrM Level)
  -> Elab (Type ErrM Level ::: Type ErrM Level)
elabType = go
  where
  go = \case
    ST.Free  n -> switch $ CV.global <$> global n
    ST.Bound n -> switch $ CV.bound  <$> bound n
    ST.Hole  n -> \ _K -> hole (n ::: _K)
    ST.Type    -> switch $ _Type
    ST.Void    -> switch $ _Void
    ST.Unit    -> switch $ _Unit
    t ST.:=> b -> switch $ fmap _check t >~> _check b
    f ST.:$  a -> switch $ _synth f $$  _check a
    a ST.:-> b -> switch $ _check a --> _check b
    l ST.:*  r -> switch $ _check l .*  _check r
    ST.Loc s b -> setSpan s . go b
    where
    _check r = tm <$> Check (go r . Just)
    _synth r = Synth (go r Nothing)


_Type :: Synth (Type ErrM Level)
_Type = Synth $ pure $ Type ::: Type

_Void :: Synth (Type ErrM Level)
_Void = Synth $ pure $ Void ::: Type

_Unit :: Synth (Type ErrM Level)
_Unit = Synth $ pure $ Unit ::: Type

(.*)
  :: Check (Type ErrM Level)
  -> Check (Type ErrM Level)
  -> Synth (Type ErrM Level)
a .* b = Synth $ do
  a' <- check (a ::: Type)
  b' <- check (b ::: Type)
  pure $ (TPrd a' b') ::: Type

infixl 7 .*

(-->)
  :: Check (Type ErrM Level)
  -> Check (Type ErrM Level)
  -> Synth (Type ErrM Level)
a --> b = Synth $ do
  a' <- check (a ::: Type)
  b' <- check (b ::: Type)
  pure $ (a' :-> b') ::: Type

infixr 2 -->

(>~>)
  :: (UName ::: Check (Type ErrM Level))
  -> Check (Type ErrM Level)
  -> Synth (Type ErrM Level)
(n ::: t) >~> b = Synth $ do
  _T <- check (t ::: Type)
  b' <- elabBinder (\ v -> v ::: _T |- check (b ::: Type))
  pure $ (n ::: _T :=> b') ::: Type

infixr 1 >~>


-- Expressions

elabExpr
  :: SE.Expr Span
  -> Maybe (Type ErrM Level)
  -> Elab (Expr ErrM Level ::: Type ErrM Level)
elabExpr = go
  where
  go = \case
    SE.Free  n -> switch $ CV.global <$> global n
    SE.Bound n -> switch $ CV.bound  <$> bound n
    SE.Hole  n -> \ _T -> hole (n ::: _T)
    f SE.:$  a -> switch $ _synth f $$ _check a
    l SE.:*  r -> check (_check l ** _check r) (pretty "product")
    SE.Unit    -> switch unit
    SE.Comp cs -> check (comp (map (SC.mapComp _check) cs)) (pretty "computation")
    SE.Loc s b -> setSpan s . go b
    where
    _check r = tm <$> Check (go r . Just)
    _synth r = Synth (go r Nothing)
    check m msg _T = expectChecked _T msg >>= \ _T -> (::: _T) <$> runCheck m _T


tlam
  :: UName
  -> Check (Expr ErrM Level)
  -> Check (Expr ErrM Level)
tlam n b = Check $ \ ty -> do
  (_ ::: _T, _B) <- expectQuantifiedType (reflow "when checking type lambda") ty
  b' <- elabBinder (\ v -> v ::: _T |- do
    _B' <- liftErr (_B v)
    check (b ::: _B'))
  pure (TLam n b')

lam
  :: UName
  -> Check (Expr ErrM Level)
  -> Check (Expr ErrM Level)
lam n b = Check $ \ _T -> do
  (_A, _B) <- expectFunctionType (reflow "when checking lambda") _T
  b' <- elabBinder (\ v -> v ::: _A |- check (b ::: _B))
  pure (Lam n b')

unit :: Synth (Expr ErrM Level)
unit = Synth . pure $ Unit ::: UnitT

(**)
  :: Check (Expr ErrM Level)
  -> Check (Expr ErrM Level)
  -> Check (Expr ErrM Level)
l ** r = Check $ \ _T -> do
  (_L, _R) <- expectProductType (reflow "when checking product") _T
  l' <- check (l ::: _L)
  r' <- check (r ::: _R)
  pure (Prd l' r')

comp
  :: [SC.Clause Check (Expr ErrM Level)]
  -> Check (Expr ErrM Level)
comp cs = do
  cs' <- traverse clause cs
  -- FIXME: extend Core to include pattern matching so this isn’t broken
  -- FIXME: extend Core to include computation types
  pure $ head cs'

clause
  :: SC.Clause Check (Expr ErrM Level)
  -> Check (Expr ErrM Level)
clause = go
  where
  go = \case
    -- FIXME: deal with other patterns.
    SC.Clause (SP.Loc _ p) b -> go (SC.Clause p b)
    SC.Clause (SP.Var n) b -> Check $ \ _T -> do
      (_A, _B) <- expectFunctionType (reflow "when checking clause") _T
      -- p' <- check (pattern p ::: _A)
      b' <- elabBinder (\ v -> v ::: _A |- check (go b ::: _B))
      pure (Lam n b')
    SC.Body e   -> e
    SC.Loc s c  -> setSpan s (go c)


pattern
  :: SP.Pattern (UName)
  -> Check (CP.Pattern (UName ::: Type ErrM Level))
pattern = go
  where
  go = \case
    SP.Wildcard -> pure CP.Wildcard
    SP.Var n    -> Check $ \ _T -> pure (CP.Var (n ::: _T))
    SP.Tuple ps -> Check $ \ _T -> CP.Tuple . toList <$> go' _T (fromList ps)
      where
      go' _T = \case
        Nil      -> Nil      <$  unify Unit _T
        Nil :> p -> (Nil :>) <$> check (go p ::: _T)
        ps  :> p -> do
          (_L, _R) <- expectProductType (reflow "when checking tuple pattern") _T
          (:>) <$> go' _L ps <*> check (go p ::: _R)
    SP.Loc s p  -> setSpan s (go p)


-- Declarations

elabDecl
  :: SD.Decl Span
  -> Check (Expr ErrM Level) ::: Check (Type ErrM Level)
elabDecl = go
  where
  go = \case
    (n ::: t) SD.:=> b ->
      let b' ::: _B = go b
      in tlam n b' ::: _check (switch (n ::: _check (elabType t) >~> _B))

    (n ::: t) SD.:-> b ->
      let b' ::: _B = go b
      -- FIXME: types and terms are bound with the same context, so the indices in the type are incremented, but arrow types don’t extend the context, so we were mishandling them.
      in lam n b' ::: _check (switch (_check (elabType t) --> (Type ::: Type |- _B)))

    t SD.:= b ->
      _check (elabExpr b) ::: _check (elabType t)

    SD.Loc s d -> setSpans s (go d)

  _check r = tm <$> Check (r . Just)

  setSpans s (t ::: _T) = setSpan s t ::: setSpan s _T


-- Modules

elabModule
  :: Has (Reader Span :+: Throw Err) sig m
  => SM.Module Span
  -> m (CM.Module ErrM)
elabModule (SM.Module s mname ds) = setSpan s . evalState (mempty @(Env.Env ErrM)) $ do
  -- FIXME: elaborate all the types first, and only then the terms
  -- FIXME: maybe figure out the graph for mutual recursion?
  defs <- for ds $ \ (SM.Def s n d) -> setSpan s $ do
    env <- get @(Env.Env ErrM)
    e' ::: _T <- runReader @Context Nil . runReader env $ do
      let e ::: t = elabDecl d
      _T <- elab $ check (t ::: Type)
      e' <- elab $ check (e ::: _T)
      pure $ e' ::: _T

    modify $ Env.insert (mname :.: n ::: _T)
    -- FIXME: extend the module
    -- FIXME: support defining types
    pure (mname :.: n, CM.DTerm e' ::: _T)

  pure $ CM.Module mname defs


-- Context

(|-) :: Has (Reader Context) sig m => Value ErrM Level ::: Type ErrM Level -> m a -> m a
t |- m = local (:>t) m

infix 1 |-


-- Failures

setSpan :: Has (Reader Span) sig m => Span -> m a -> m a
setSpan = local . const

printType :: HasCallStack => Has (Reader Context :+: Reader Span :+: Throw Err) sig m => Type ErrM Level -> m ErrDoc
-- FIXME: this is still resulting in out of bounds printing
printType t = do
  ctx <- ask @Context
  let go Nil = pure Nil
      go (as:>a) = do
        as' <- go as
        a' <- P.printCoreValue' as' a
        pure $ as' :> a'
  ctx' <- rethrow $ go (tm <$> ctx)
  P.getPrint <$> rethrow (P.printCoreValue' ctx' t)

err :: Has (Throw Err) sig m => ErrDoc -> m a
err = throwError . (`Err` []) . group

hole :: Has (Reader Context :+: Reader Span :+: Throw Err) sig m => (T.Text ::: Maybe (Type ErrM Level)) -> m (a ::: Type ErrM Level)
hole (n ::: t) = case t of
  Just t  -> do
    t' <- printType t
    err $ fillSep [pretty "found", pretty "hole", pretty n, colon, t' ]
  Nothing -> couldNotSynthesize (fillSep [ pretty "hole", pretty n ])

mismatch :: Has (Throw Err) sig m => ErrDoc -> ErrDoc -> ErrDoc -> m a
mismatch msg exp act = err $ msg
  </> pretty "expected:" <> print exp
  </> pretty "  actual:" <> print act
  where
  -- line things up nicely for e.g. wrapped function types
  print = nest 2 . (flatAlt (line <> stimes (3 :: Int) space) mempty <>)

couldNotUnify :: (HasCallStack, Has (Reader Context :+: Reader Span :+: Throw Err) sig m) => Type ErrM Level -> Type ErrM Level -> m a
couldNotUnify t1 t2 = do
  t1' <- printType t1
  t2' <- printType t2
  mismatch (reflow "mismatch") t2' t1'

couldNotSynthesize :: Has (Throw Err) sig m => ErrDoc -> m a
couldNotSynthesize msg = err $ reflow "could not synthesize a type for" <> softline <> msg

freeVariable :: Has (Throw Err) sig m => ErrDoc -> m a
freeVariable v = err $ fillSep [reflow "variable not in scope:", v]

expectChecked :: Has (Throw Err) sig m => Maybe (Type ErrM Level) -> ErrDoc -> m (Type ErrM Level)
expectChecked t msg = maybe (couldNotSynthesize msg) pure t


-- Patterns

expectMatch :: (HasCallStack, Has (Reader Context :+: Reader Span :+: Throw Err) sig m) => (Type ErrM Level -> Maybe out) -> ErrDoc -> ErrDoc -> Type ErrM Level -> m out
expectMatch pat exp s _T = do
  _T' <- printType _T
  maybe (mismatch s exp _T') pure (pat _T)

expectQuantifiedType :: (HasCallStack, Has (Reader Context :+: Reader Span :+: Throw Err) sig m) => ErrDoc -> Type ErrM Level -> m (UName ::: Type ErrM Level, Type ErrM Level -> ErrM (Type ErrM Level))
expectQuantifiedType = expectMatch unForAll (pretty "{_} -> _")

expectFunctionType :: (HasCallStack, Has (Reader Context :+: Reader Span :+: Throw Err) sig m) => ErrDoc -> Type ErrM Level -> m (Type ErrM Level, Type ErrM Level)
expectFunctionType = expectMatch unArrow (pretty "_ -> _")

expectProductType :: (HasCallStack, Has (Reader Context :+: Reader Span :+: Throw Err) sig m) => ErrDoc -> Type ErrM Level -> m (Type ErrM Level, Type ErrM Level)
expectProductType = expectMatch unProductT (pretty "(_, _)")
