{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Elab
( Context
, implicit
, elab
, Elab(..)
, Check(..)
, Synth(..)
, check
, switch
, unify
  -- * Types
, elabType
, tglobal
, tbound
, _Type
, _Unit
, (.$)
, (.*)
, (-->)
, (>~>)
  -- * Expressions
, elabExpr
, eglobal
, ebound
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
import           Control.Category ((>>>))
import           Control.Effect.Parser.Span (Span(..))
import           Data.Bifunctor (bimap, first)
import qualified Data.IntMap as IntMap
import qualified Data.Text as T
import           Data.Traversable (for)
import           Facet.Carrier.Error.Context
import qualified Facet.Core as C
import           Facet.Core.Type
import qualified Facet.Env as Env
import           Facet.Name (MName(..), Name(..), QName(..), prettyNameWith)
import qualified Facet.Name as N
import           Facet.Pretty (reflow)
import qualified Facet.Print as P
import qualified Facet.Surface.Comp as C
import qualified Facet.Surface.Decl as D
import qualified Facet.Surface.Expr as E
import qualified Facet.Surface.Module as M
import qualified Facet.Surface.Type as T
import           Facet.Syntax
import           Prelude hiding ((**))
import           Silkscreen (colon, fillSep, group, pretty, softline, (<+>), (</>))

type Context = IntMap.IntMap Type

implicit :: Env.Env
implicit = Env.fromList [ (N.T (N.TName (T.pack "Type")), MName (T.pack "Facet") ::: C._Type) ]

elab :: Applicative m => MName -> Span -> Env.Env -> Context -> Elab m a -> m (Either (Span, P.Print) a)
elab n s e c (Elab m) = runError (curry (pure . Left)) (pure . Right) s (m n e c)

newtype Elab m a = Elab (MName -> Env.Env -> Context -> ErrorC Span P.Print m a)
  deriving (Algebra (Reader MName :+: Reader Env.Env :+: Reader Context :+: Error P.Print :+: Reader Span :+: sig), Applicative, Functor, Monad) via ReaderC MName (ReaderC Env.Env (ReaderC Context (ErrorC Span P.Print m)))


newtype Check m a = Check { runCheck :: Type -> m a }
  deriving (Algebra (Reader Type :+: sig), Applicative, Functor, Monad) via ReaderC Type m

newtype Synth m a = Synth { synth :: m (a ::: Type) }

instance Functor m => Functor (Synth m) where
  fmap f (Synth m) = Synth (first f <$> m)

check :: (Check m a ::: Type) -> m a
check = uncurryAnn runCheck

switch :: Has (Error P.Print) sig m => Synth m a -> Check m a
switch s = Check $ \ _T -> do
  a ::: _T' <- synth s
  a <$ unify _T _T'

unify :: Has (Error P.Print) sig m => Type -> Type -> m ()
unify t1 t2 = go t1 t2
  where
  go = curry $ bimap out out >>> \case
    (Type,      Type)       -> pure ()
    (Unit,      Unit)       -> pure ()
    (l1 :* r1,  l2 :* r2)   -> go l1 l2 *> go r1 r2
    -- FIXME: we try to unify Type-the-global with Type-the-constant
    -- FIXME: resolve globals to try to progress past certain inequalities
    (f1 :$ a1,  f2 :$ a2)
      | f1 == f2
      , Just _ <- goS a1 a2 -> pure ()
    (a1 :-> b1, a2 :-> b2)  -> go a1 a2 *> go b1 b2
    (t1 :=> b1, t2 :=> b2)  -> go (ty t1) (ty t2) *> go b1 b2
    -- FIXME: build and display a diff of the root types
    (t1, t2) -> couldNotUnify (In t1) (In t2)
  goS Nil        Nil        = Just (pure ())
  goS (i1 :> l1) (i2 :> l2) = (*>) <$> goS i1 i2 <*> Just (go l1 l2)
  goS _          _          = Nothing


-- General

bound :: (Has (Error P.Print) sig m, Has (Reader Context) sig m) => Name -> (Name -> e) -> (Int -> P.Print) -> Synth m e
bound n with var = Synth $ asks (IntMap.lookup (id' n)) >>= \case
  Just b  -> pure (with n ::: b)
  Nothing -> freeVariable (prettyNameWith var n)

app :: Has (Error P.Print) sig m => (a -> a -> a) -> Synth m a -> Check m a -> Synth m a
app ($$) f a = Synth $ do
  f' ::: _F <- synth f
  (_A, _B) <- expectFunctionType (pretty "in application") _F
  a' <- check (a ::: _A)
  pure $ f' $$ a' ::: _B


-- Types

elabType :: (Has (Error P.Print) sig m, Has (Reader Context) sig m, Has (Reader Env.Env) sig m, Has (Reader Span) sig m) => (T.Type ::: Maybe Type) -> m (Type ::: Type)
elabType (t ::: _K) = T.fold alg t _K
  where
  alg t _K = case t of
    T.Free  n -> validate =<< synth (tglobal n)
    T.Bound n -> validate =<< synth (tbound n)
    T.Hole  n -> hole (n ::: _K)
    T.Type    -> validate =<< synth _Type
    T.Void    -> validate =<< synth _Void
    T.Unit    -> validate =<< synth _Unit
    t T.:=> b -> validate =<< synth (fmap _check t >~> _check b)
    f T.:$  a -> validate =<< synth (_synth f .$  _check a)
    a T.:-> b -> validate =<< synth (_check a --> _check b)
    l T.:*  r -> validate =<< synth (_check l .*  _check r)
    T.Loc s b -> local (const s) $ b _K
    where
    _check r = tm <$> Check (r . Just)
    _synth r = Synth (r Nothing)
    validate r@(_T ::: _K') = case _K of
      Just _K -> r <$ unify _K' _K
      _       -> pure r

tglobal :: (Has (Reader Env.Env) sig m, C.Type ty, Has (Error P.Print) sig m) => N.DName -> Synth m ty
tglobal n = Synth $ asks (Env.lookup n) >>= \case
  Just b  -> pure (C.tglobal (tm b :.: n) ::: ty b)
  Nothing -> freeVariable (pretty n)

tbound :: (C.Type ty, Has (Error P.Print) sig m, Has (Reader Context) sig m) => Name -> Synth m ty
tbound n = bound n C.tbound P.tvar

_Type :: (Applicative m, C.Type t) => Synth m t
_Type = Synth $ pure $ C._Type ::: C._Type

_Void :: (Applicative m, C.Type t) => Synth m t
_Void = Synth $ pure $ C._Void ::: C._Type

_Unit :: (Applicative m, C.Type t) => Synth m t
_Unit = Synth $ pure $ C._Unit ::: C._Type

(.$) :: (Has (Error P.Print) sig m, C.Type t) => Synth m t -> Check m t -> Synth m t
(.$) = app (C..$)

infixl 9 .$

(.*) :: (Monad m, C.Type t) => Check m t -> Check m t -> Synth m t
a .* b = Synth $ do
  a' <- check (a ::: C._Type)
  b' <- check (b ::: C._Type)
  pure $ a' C..* b' ::: C._Type

infixl 7 .*

(-->) :: (Monad m, C.Type t) => Check m t -> Check m t -> Synth m t
a --> b = Synth $ do
  a' <- check (a ::: C._Type)
  b' <- check (b ::: C._Type)
  pure $ (a' C.--> b') ::: C._Type

infixr 2 -->

(>~>)
  :: Has (Reader Context) sig m
  => (Name ::: Check m Type)
  -> Check m Type
  -> Synth m Type
(n ::: t) >~> b = Synth $ do
  _T <- check (t ::: C._Type)
  ftb' <- n ::: _T |- ((n ::: _T) C.>=>) <$> check (b ::: C._Type)
  pure $ ftb' ::: C._Type

infixr 1 >~>


-- Expressions

elabExpr :: (Has (Error P.Print) sig m, Has (Reader Context) sig m, Has (Reader Env.Env) sig m, Has (Reader Span) sig m, C.Expr expr) => (E.Expr ::: Maybe Type) -> m (expr ::: Type)
elabExpr (t ::: _T) = E.fold alg t _T
  where
  alg t _T = case t of
    E.Free  n -> validate =<< synth (eglobal n)
    E.Bound n -> validate =<< synth (ebound n)
    E.Hole  n -> hole (n ::: _T)
    f E.:$  a -> validate =<< synth (_synth f $$  _check a)
    l E.:*  r -> check (_check l **  _check r ::: _T) (pretty "product")
    E.Unit    -> validate =<< synth unit
    E.Comp c  -> check (comp (_check <$> c) ::: _T) (pretty "computation")
    E.Loc s b -> local (const s) $ b _T
    where
    _check r = tm <$> Check (r . Just)
    _synth r = Synth (r Nothing)
    check (m ::: _T) msg = expectChecked _T msg >>= \ _T -> (::: _T) <$> runCheck m _T
    validate r@(_ ::: _T') = case _T of
      Just _T -> r <$ unify _T' _T
      _       -> pure r

eglobal :: (Has (Reader Env.Env) sig m, C.Expr expr, Has (Error P.Print) sig m) => N.DName -> Synth m expr
eglobal n = Synth $ asks (Env.lookup n) >>= \case
  Just b  -> pure (C.global (tm b :.: n) ::: ty b)
  Nothing -> freeVariable (pretty n)

ebound :: (C.Expr expr, Has (Error P.Print) sig m, Has (Reader Context) sig m) => Name -> Synth m expr
ebound n = bound n C.bound P.evar

($$) :: (C.Expr expr, Has (Error P.Print) sig m) => Synth m expr -> Check m expr -> Synth m expr
($$) = app (C.$$)

tlam :: (Has (Reader Context) sig m, C.Expr expr, Has (Error P.Print) sig m) => Name -> Check m expr -> Check m expr
tlam n b = Check $ \ ty -> do
  (n', _T, _B) <- expectQuantifiedType (reflow "when checking type lambda") ty
  n' ::: _T |- C.tlam n <$> check (b ::: _B)

lam :: (Has (Reader Context) sig m, C.Expr expr, Has (Error P.Print) sig m) => Name -> Check m expr -> Check m expr
lam n b = Check $ \ _T -> do
  (_A, _B) <- expectFunctionType (reflow "when checking lambda") _T
  n ::: _A |- C.lam n <$> check (b ::: _B)

unit :: (Applicative m, C.Expr t) => Synth m t
unit = Synth . pure $ C.unit ::: C._Unit

(**) :: (C.Expr expr, Has (Error P.Print) sig m) => Check m expr -> Check m expr -> Check m expr
l ** r = Check $ \ _T -> do
  (_L, _R) <- expectProductType (reflow "when checking product") _T
  l' <- check (l ::: _L)
  r' <- check (r ::: _R)
  pure (l' C.** r')

comp :: (Has (Error P.Print) sig m, Has (Reader Context) sig m, Has (Reader Span) sig m, C.Expr expr) => C.Comp (Check m expr) -> Check m expr
comp = C.fold $ \case
  C.Cases cs -> Check $ \ _T -> do
    (_A, _B) <- expectFunctionType (reflow "when checking computation") _T
    cs' <- for cs $ \ (n, b) ->
      n ::: _A |- (,) n <$> check (b ::: _B)
    -- FIXME: extend Core to include computation types
    -- FIXME: extend Core to include pattern matching so this isn’t broken
    pure $ uncurry C.lam $ head cs'
  C.Expr e   -> e
  C.Loc s c  -> local (const s) c


-- Declarations

elabDecl :: (Has (Error P.Print) sig m, Has (Reader Context) sig m, Has (Reader Env.Env) sig m, Has (Reader Span) sig m, C.Expr expr) => D.Decl -> m (Check m expr ::: Type)
elabDecl = D.fold alg
  where
  alg = \case
    (n ::: t) D.:=> b -> do
      _T ::: _  <- elabType (t ::: Just C._Type)
      b' ::: _B <- n ::: _T |- b
      pure $ tlam n b' ::: ((n ::: _T) C.>=> _B)

    (n ::: t) D.:-> b -> do
      _T ::: _  <- elabType (t ::: Just C._Type)
      b' ::: _B <- n ::: _T |- b
      pure $ lam n b' ::: (_T C.--> _B)

    t D.:= b -> do
      _T ::: _ <- elabType (t ::: Just C._Type)
      pure $ _check (elabExpr . (b :::)) ::: _T

    D.Loc s d -> local (const s) d
  _check r = tm <$> Check (r . Just)


-- Modules

elabModule :: (Has (Error P.Print) sig m, Has (Reader Context) sig m, Has (Reader Env.Env) sig m, Has (Reader MName) sig m, Has (Reader Span) sig m, C.Expr expr, C.Type ty, C.Module expr ty mod) => M.Module -> m mod
elabModule = M.fold alg
  where
  alg = \case
    M.Module n ds -> C.module' n <$> sequenceA ds

    M.Def n d -> do
      e ::: _T <- elabDecl d
      e' <- check (e ::: _T)
      mname <- ask
      pure $ C.defTerm (mname :.: n) (interpret _T := e')

    M.Loc s d -> local (const s) d


-- Context

(|-) :: Has (Reader Context) sig m => Name ::: Type -> m a -> m a
n ::: t |- m = local (IntMap.insert (id' n) t) m

infix 1 |-


-- Failures

err :: Has (Error P.Print) sig m => P.Print -> m a
err = throwError . group

hole :: Has (Error P.Print) sig m => (T.Text ::: Maybe Type) -> m (a ::: Type)
hole (n ::: t) = case t of
  Just t  -> err $ fillSep [pretty "found", pretty "hole", pretty n, colon, interpret t]
  Nothing -> couldNotSynthesize (fillSep [ pretty "hole", pretty n ])

mismatch :: Has (Error P.Print) sig m => P.Print -> P.Print -> P.Print -> m a
mismatch msg exp act = err $ msg
  </> pretty "expected:" <+> exp
  </> pretty "  actual:" <+> act

couldNotUnify :: Has (Error P.Print) sig m => Type -> Type -> m a
couldNotUnify t1 t2 = mismatch (reflow "could not unify") (interpret t2) (interpret t1)

couldNotSynthesize :: Has (Error P.Print) sig m => P.Print -> m a
couldNotSynthesize msg = err $ reflow "could not synthesize a type for" <> softline <> msg

freeVariable :: Has (Error P.Print) sig m => P.Print -> m a
freeVariable v = err $ fillSep [reflow "variable not in scope:", v]


-- Patterns

expectChecked :: Has (Error P.Print) sig m => Maybe Type -> P.Print -> m Type
expectChecked t msg = maybe (couldNotSynthesize msg) pure t

expectQuantifiedType :: Has (Error P.Print) sig m => P.Print -> Type -> m (Name, Type, Type)
expectQuantifiedType s = out >>> \case
  (n ::: _T) :=> _B -> pure (n, _T, _B)
  _T                -> mismatch s (pretty "{_} -> _") (interpret (In _T))

expectFunctionType :: Has (Error P.Print) sig m => P.Print -> Type -> m (Type, Type)
expectFunctionType s = out >>> \case
  _A :-> _B -> pure (_A, _B)
  _T        -> mismatch s (pretty "_ -> _") (interpret (In _T))

expectProductType :: Has (Error P.Print) sig m => P.Print -> Type -> m (Type, Type)
expectProductType s = out >>> \case
  _A :* _B -> pure (_A, _B)
  _T       -> mismatch s (pretty "(_, _)") (interpret (In _T))
