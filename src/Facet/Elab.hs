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
( runErrM
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
import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Category ((>>>))
import           Control.Effect.Lift
import           Control.Effect.Parser.Span (Span(..))
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
import           Facet.Name (Index(..), Level(..), QName(..), UName, incrLevel, indexToLevel)
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
import           Prelude hiding ((**))
import           Silkscreen (colon, fillSep, flatAlt, group, line, nest, pretty, softline, space, (</>))

runErrM :: Span -> ErrorC Span Err Identity a -> Either (Span, Err) a
runErrM s = run . runError (curry (Identity . Left)) (Identity . Right) s

type Context = Stack (UName ::: Type Elab Level)

elab :: Has (Reader Context :+: Reader (Env.Env Elab) :+: Reader Span :+: Throw Err) sig m => Elab a -> m a
elab (Elab m) = do
  ctx <- ask
  env <- ask
  span <- ask
  run (runError (\ s e -> pure (setSpan s (throwError e))) (pure . pure) span (runReader ctx (runReader env m)))

-- FIXME: can we generalize this to a rank-n quantified action over any context providing these effects?
newtype Elab a = Elab (ReaderC (Env.Env Elab) (ReaderC Context (ErrorC Span Err Identity)) a)
  deriving (Algebra (Reader (Env.Env Elab) :+: Reader Context :+: Error Err :+: Reader Span :+: Lift Identity), Applicative, Functor, Monad)


newtype Check a = Check { runCheck :: Type Elab Level -> Elab a }
  deriving (Algebra (Reader (Type Elab Level) :+: Reader (Env.Env Elab) :+: Reader Context :+: Error Err :+: Reader Span :+: Lift Identity), Applicative, Functor, Monad) via ReaderC (Type Elab Level) Elab

newtype Synth a = Synth { synth :: Elab (a ::: Type Elab Level) }

instance Functor Synth where
  fmap f (Synth m) = Synth (first f <$> m)

check :: (Check a ::: Type Elab Level) -> Elab a
check = uncurryAnn runCheck


unify
  :: Type Elab Level
  -> Type Elab Level
  -> Elab (Type Elab Level)
unify t1 t2 = t2 <$ go (Level 0) t1 t2
  where
  go n t1 t2 = case (t1, t2) of
    (Type,      Type)       -> pure ()
    (Unit,      Unit)       -> pure ()
    -- FIXME: we try to unify Type-the-global with Type-the-constant
    -- FIXME: resolve globals to try to progress past certain inequalities
    (f1 :$ a1,  f2 :$ a2)
      | f1 == f2
      , Just _ <- goS a1 a2 -> pure ()
    (a1 :-> b1, a2 :-> b2)  -> go n a1 a2 *> go n b1 b2
    (t1 :=> b1, t2 :=> b2)  -> do
      let v = CV.bound n
      go n (ty t1) (ty t2)
      b1' <- elab $ b1 v
      b2' <- elab $ b2 v
      go (incrLevel n) b1' b2'
    (TPrd l1 r1, TPrd l2 r2)   -> go n l1 l2 *> go n r1 r2
    (Prd  l1 r1, Prd  l2 r2)   -> go n l1 l2 *> go n r1 r2
    -- FIXME: build and display a diff of the root types
    _                       -> couldNotUnify t1 t2
    where
    goS Nil        Nil        = Just (pure ())
    goS (i1 :> l1) (i2 :> l2) = (*>) <$> goS i1 i2 <*> Just (go n l1 l2)
    goS _          _          = Nothing


-- General

switch
  :: Synth a
  -> Maybe (Type Elab Level)
  -> Elab (a ::: Type Elab Level)
switch (Synth m) = \case
  Just _K -> m >>= \ (a ::: _K') -> (a :::) <$> unify _K' _K
  _       -> m

global
  :: N.DName
  -> Synth QName
global n = Synth $ asks (Env.lookup n) >>= \case
  Just b  -> pure (tm b :.: n ::: ty b)
  Nothing -> freeVariable (pretty n)

bound
  :: Index
  -> Synth Level
bound n = Synth $ do
  ctx <- ask @Context
  case ctx !? getIndex n of
    Just (_ ::: _T) -> pure (indexToLevel (length ctx) n ::: _T)
    Nothing         -> err (reflow "bad context")

($$)
  :: Synth (Value Elab Level)
  -> Check (Value Elab Level)
  -> Synth (Value Elab Level)
f $$ a = Synth $ do
  f' ::: _F <- synth f
  (_A, _B) <- expectFunctionType (pretty "in application") _F
  a' <- check (a ::: _A)
  (::: _B) <$> f' CV.$$ a'


-- Types

elabType
  :: ST.Type
  -> Maybe (Type Elab Level)
  -> Elab (Type Elab Level ::: Type Elab Level)
elabType = go
  where
  go = ST.out >>> \case
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


_Type :: Synth (Type Elab Level)
_Type = Synth $ pure $ Type ::: Type

_Void :: Synth (Type Elab Level)
_Void = Synth $ pure $ Void ::: Type

_Unit :: Synth (Type Elab Level)
_Unit = Synth $ pure $ Unit ::: Type

(.*)
  :: Check (Type Elab Level)
  -> Check (Type Elab Level)
  -> Synth (Type Elab Level)
a .* b = Synth $ do
  a' <- check (a ::: Type)
  b' <- check (b ::: Type)
  pure $ (TPrd a' b') ::: Type

infixl 7 .*

(-->)
  :: Check (Type Elab Level)
  -> Check (Type Elab Level)
  -> Synth (Type Elab Level)
a --> b = Synth $ do
  a' <- check (a ::: Type)
  b' <- check (b ::: Type)
  pure $ (a' :-> b') ::: Type

infixr 2 -->

(>~>)
  :: (UName ::: Check (Type Elab Level))
  -> Check (Type Elab Level)
  -> Synth (Type Elab Level)
(n ::: t) >~> b = Synth $ do
  _T <- check (t ::: Type)
  -- FIXME: this is wrong, we should push this onto the context
  pure $ (n ::: _T :=> \ v -> n ::: _T |- check (b ::: Type)) ::: Type

infixr 1 >~>


-- Expressions

elabExpr
  :: SE.Expr
  -> Maybe (Type Elab Level)
  -> Elab (Expr Elab Level ::: Type Elab Level)
elabExpr = go
  where
  go = SE.out >>> \case
    SE.Free  n -> switch $ CV.global <$> global n
    SE.Bound n -> switch $ CV.bound  <$> bound n
    SE.Hole  n -> \ _T -> hole (n ::: _T)
    f SE.:$  a -> switch $ _synth f $$ _check a
    l SE.:*  r -> check (_check l ** _check r) (pretty "product")
    SE.Unit    -> switch unit
    SE.Comp cs -> check (comp (map (fmap _check) cs)) (pretty "computation")
    SE.Loc s b -> setSpan s . go b
    where
    _check r = tm <$> Check (go r . Just)
    _synth r = Synth (go r Nothing)
    check m msg _T = expectChecked _T msg >>= \ _T -> (::: _T) <$> runCheck m _T


tlam
  :: UName
  -> Check (Expr Elab Level)
  -> Check (Expr Elab Level)
tlam n b = Check $ \ ty -> do
  (_T, _B) <- expectQuantifiedType (reflow "when checking type lambda") ty
  pure (TLam n (\ v -> _T |- do
    _B' <- elab (_B v)
    check (b ::: _B')))

lam
  :: UName
  -> Check (Expr Elab Level)
  -> Check (Expr Elab Level)
lam n b = Check $ \ _T -> do
  (_A, _B) <- expectFunctionType (reflow "when checking lambda") _T
  n ::: _A |- do
    -- FIXME: this is wrong, we should check under the binder
    b' <- check (b ::: _B)
    pure (Lam n (b' CV.$$))

unit :: Synth (Expr Elab Level)
unit = Synth . pure $ Unit ::: UnitT

(**)
  :: Check (Expr Elab Level)
  -> Check (Expr Elab Level)
  -> Check (Expr Elab Level)
l ** r = Check $ \ _T -> do
  (_L, _R) <- expectProductType (reflow "when checking product") _T
  l' <- check (l ::: _L)
  r' <- check (r ::: _R)
  pure (Prd l' r')

comp
  :: [SC.Clause (Check (Expr Elab Level))]
  -> Check (Expr Elab Level)
comp cs = do
  cs' <- traverse clause cs
  -- FIXME: extend Core to include pattern matching so this isn’t broken
  -- FIXME: extend Core to include computation types
  pure $ head cs'

clause
  :: SC.Clause (Check (Expr Elab Level))
  -> Check (Expr Elab Level)
clause = go
  where
  go = SC.out >>> \case
    -- FIXME: deal with other patterns.
    SC.Clause (SP.In _ (SP.Var n)) b -> Check $ \ _T -> do
      (_A, _B) <- expectFunctionType (reflow "when checking clause") _T
      -- p' <- check (pattern p ::: _A)
      n ::: _A |- do
        -- FIXME: this is wrong.
        pure (Lam n (\ v -> check (go b ::: _B)))
    SC.Body e   -> e
    SC.Loc s c  -> setSpan s (go c)


pattern
  :: SP.Pattern (UName)
  -> Check (CP.Pattern (UName ::: Type Elab Level))
pattern = go
  where
  go (SP.In s p) = setSpan s $ case p of
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


-- Declarations

elabDecl
  :: SD.Decl
  -> Check (Expr Elab Level) ::: Check (Type Elab Level)
elabDecl = go
  where
  go (SD.In s d) = setSpans s $ case d of
    (n ::: t) SD.:=> b ->
      let b' ::: _B = go b
      in tlam n b' ::: _check (switch (n ::: _check (elabType t) >~> _B))

    (n ::: t) SD.:-> b ->
      let b' ::: _B = go b
      in lam n b' ::: _check (switch (_check (elabType t) --> _B))

    t SD.:= b ->
      _check (elabExpr b) ::: _check (elabType t)

  _check r = tm <$> Check (r . Just)

  setSpans s (t ::: _T) = setSpan s t ::: setSpan s _T


-- Modules

elabModule
  :: Has (Reader Span :+: Throw Err) sig m
  => SM.Module
  -> m (CM.Module Elab)
elabModule (SM.Module s mname ds) = setSpan s . evalState (mempty @(Env.Env Elab)) $ do
  -- FIXME: elaborate all the types first, and only then the terms
  -- FIXME: maybe figure out the graph for mutual recursion?
  defs <- for ds $ \ (SM.Def s n d) -> setSpan s $ do
    env <- get @(Env.Env Elab)
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

(|-) :: Has (Reader Context) sig m => UName ::: Type Elab Level -> m a -> m a
t |- m = local (:>t) m

infix 1 |-


-- Failures

setSpan :: Has (Reader Span) sig m => Span -> m a -> m a
setSpan = local . const

printType :: Has (Reader Context :+: Reader (Env.Env Elab) :+: Reader Span :+: Throw Err) sig m => Type Elab Level -> m ErrDoc
-- FIXME: this is almost certainly going to show the wrong thing because we don’t incorporate types from the context
printType t = P.getPrint <$> elab (P.printCoreValue' Nil t)

err :: Has (Throw Err) sig m => ErrDoc -> m a
err = throwError . (`Err` []) . group

hole :: Has (Reader Context :+: Reader (Env.Env Elab) :+: Reader Span :+: Throw Err) sig m => (T.Text ::: Maybe (Type Elab Level)) -> m (a ::: Type Elab Level)
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

couldNotUnify :: Has (Reader Context :+: Reader (Env.Env Elab) :+: Reader Span :+: Throw Err) sig m => Type Elab Level -> Type Elab Level -> m a
couldNotUnify t1 t2 = do
  t1' <- printType t1
  t2' <- printType t2
  mismatch (reflow "mismatch") t2' t1'

couldNotSynthesize :: Has (Throw Err) sig m => ErrDoc -> m a
couldNotSynthesize msg = err $ reflow "could not synthesize a type for" <> softline <> msg

freeVariable :: Has (Throw Err) sig m => ErrDoc -> m a
freeVariable v = err $ fillSep [reflow "variable not in scope:", v]

expectChecked :: Has (Throw Err) sig m => Maybe (Type Elab Level) -> ErrDoc -> m (Type Elab Level)
expectChecked t msg = maybe (couldNotSynthesize msg) pure t


-- Patterns

expectMatch :: Has (Reader Context :+: Reader (Env.Env Elab) :+: Reader Span :+: Throw Err) sig m => (Type Elab Level -> Maybe out) -> ErrDoc -> ErrDoc -> Type Elab Level -> m out
expectMatch pat exp s _T = do
  _T' <- printType _T
  maybe (mismatch s exp _T') pure (pat _T)

expectQuantifiedType :: Has (Reader Context :+: Reader (Env.Env Elab) :+: Reader Span :+: Throw Err) sig m => ErrDoc -> Type Elab Level -> m (UName ::: Type Elab Level, Type Elab Level -> Elab (Type Elab Level))
expectQuantifiedType = expectMatch unForAll (pretty "{_} -> _")

expectFunctionType :: Has (Reader Context :+: Reader (Env.Env Elab) :+: Reader Span :+: Throw Err) sig m => ErrDoc -> Type Elab Level -> m (Type Elab Level, Type Elab Level)
expectFunctionType = expectMatch unArrow (pretty "_ -> _")

expectProductType :: Has (Reader Context :+: Reader (Env.Env Elab) :+: Reader Span :+: Throw Err) sig m => ErrDoc -> Type Elab Level -> m (Type Elab Level, Type Elab Level)
expectProductType = expectMatch unProductT (pretty "(_, _)")
