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
) where

import           Control.Algebra
import           Control.Carrier.Reader
import           Control.Effect.Error
import           Control.Effect.Parser.Span (Span(..))
import           Data.Bifunctor (first)
import qualified Data.IntMap as IntMap
import qualified Data.Text as T
import qualified Facet.Core as C
import qualified Facet.Env as Env
import           Facet.Name (Name(..), prettyNameWith)
import qualified Facet.Print as P
import qualified Facet.Surface as S
import qualified Facet.Surface.Expr as SE
import qualified Facet.Surface.Type as ST
import           Facet.Syntax
import           Facet.Type
import           Prelude hiding ((**))
import           Silkscreen (fillSep, group, pretty, (<+>), (</>))

type Context = IntMap.IntMap Type

implicit :: Env.Env
implicit = Env.fromList [ (T.pack "Type", C._Type) ]

elab :: (Elab m a ::: Maybe Type) -> m a
elab = runEnv implicit mempty . uncurryAnn runElab

runEnv :: Env.Env -> Context -> EnvC m a -> m a
runEnv e c m = runEnvC m e c

newtype EnvC m a = EnvC { runEnvC :: Env.Env -> Context -> m a }
  deriving (Algebra (Reader Env.Env :+: Reader Context :+: sig), Applicative, Functor, Monad) via ReaderC Env.Env (ReaderC Context m)

-- FIXME: elaborate Expr instead of doing the final tagless dance.
newtype Elab m a = Elab { runElab :: Maybe Type -> EnvC m a }
  deriving (Algebra (Reader (Maybe Type) :+: Reader Env.Env :+: Reader Context :+: sig), Applicative, Functor, Monad) via ReaderC (Maybe Type) (EnvC m)

fromCheck :: Has (Error P.Print) sig m => Check m a -> Elab m (a ::: Type)
fromCheck m = Elab $ \case
  Just t  -> (::: t) <$> check (m ::: t)
  Nothing -> couldNotSynthesize

toCheck :: Has (Error P.Print) sig m => Elab m (a ::: Type) -> Check m a
toCheck m = Check $ \ _T -> do
  a ::: _T' <- runElab m (Just _T)
  a <$ unify _T _T'

fromSynth :: Has (Error P.Print) sig m => Synth m a -> Elab m (a ::: Type)
fromSynth (Synth m) = Elab $ \case
  Just _T -> do
    a ::: _T' <- m
    (a ::: _T') <$ unify _T _T'
  Nothing -> m

toSynth :: Elab m (a ::: Type) -> Synth m a
toSynth (Elab m) = Synth (m Nothing)

instance Has (Reader Span) sig m => S.Located (Elab m a) where
  locate = local . const

instance Has (Error P.Print) sig m => S.Type (Elab m (Type ::: Type)) where
  tglobal = fromSynth . tglobal
  tbound n = fromSynth (tbound n)
  (n ::: t) >~> b = fromSynth $ (n ::: toCheck t) >~> toCheck b
  a --> b = fromSynth $ toCheck a --> toCheck b
  f .$  a = fromSynth $ toSynth f .$  toCheck a
  l .*  r = fromSynth $ toCheck l .*  toCheck r

  _Unit = fromSynth _Unit
  _Type = fromSynth _Type

instance (C.Expr expr, Has (Error P.Print) sig m) => S.Expr (Elab m (expr ::: Type)) where
  global = fromSynth . eglobal
  bound n = fromSynth (ebound n)
  lam n b = fromCheck $ lam n (toCheck b)
  f $$ a = fromSynth $ toSynth f $$ toCheck a
  unit = tbd
  _ ** _ = tbd

-- FIXME: this should probably elaborate to nested elaborators, one at type level, producing one at expression level
instance (C.Expr expr, Has (Error P.Print) sig m) => S.Decl (Elab m (expr ::: Type)) (Elab m (Type ::: Type)) (Elab m (expr ::: Type)) where
  t .= b = Elab $ \ _T -> do -- FIXME: what are we supposed to do with _T? what’s the type of a declaration anyway?
    _T' ::: _ <- runElab t (Just C._Type)
    b' ::: _ <- runElab b (Just _T')
    pure $ b' ::: _T'

  (n ::: t) >=> b = Elab $ \ _T -> do
    _T ::: _ <- runElab t (Just C._Type)
    b' ::: _B <- n ::: _T |- runElab b Nothing
    pure $ C.tlam n b' ::: ((n ::: _T) C.==> _B)

  (n ::: t) >-> b = Elab $ \ _T -> do
    _T ::: _ <- runElab t (Just C._Type)
    b' ::: _B <- n ::: _T |- runElab b Nothing
    pure $ C.lam n b' ::: (_T C.--> _B)

instance (C.Expr expr, C.Type ty, C.Module expr ty mod, Has (Error P.Print) sig m) => S.Module (Elab m (expr ::: Type)) (Elab m (Type ::: Type)) (Elab m (expr ::: Type)) (Elab m mod) where
  n .:. d = do
    e ::: _T <- d -- FIXME: check _T at Type, check e at _T -- d should probably be two separate elaborators
    pure $ S.getDName n C..:. interpret _T := e


newtype Check m a = Check { runCheck :: Type -> EnvC m a }
  deriving (Algebra (Reader Type :+: Reader Env.Env :+: Reader Context :+: sig), Applicative, Functor, Monad) via ReaderC Type (EnvC m)

newtype Synth m a = Synth { synth :: EnvC m (a ::: Type) }

instance Functor m => Functor (Synth m) where
  fmap f (Synth m) = Synth (first f <$> m)

check :: (Check m a ::: Type) -> EnvC m a
check = uncurryAnn runCheck

switch :: Has (Error P.Print) sig m => Synth m a -> Check m a
switch s = Check $ \ _T -> do
  a ::: _T' <- synth s
  a <$ unify _T _T'

unify :: Has (Error P.Print) sig m => Type -> Type -> m ()
unify t1 t2 = go t1 t2
  where
  go = curry $ \case
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
    (t1, t2) -> couldNotUnify t1 t2
  goS Nil        Nil        = Just (pure ())
  goS (i1 :> l1) (i2 :> l2) = (*>) <$> goS i1 i2 <*> Just (go l1 l2)
  goS _          _          = Nothing


-- General

bound :: Has (Error P.Print) sig m => Name -> (Name -> e) -> (Int -> P.Print) -> Synth m e
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

elabType :: (Has (Error P.Print) sig m, Has (Reader Span) sig m) => (ST.Type ::: Maybe Type) -> EnvC m (Type ::: Type)
elabType (t ::: _K) = ST.fold alg t _K
  where
  alg t _K = case t of
    ST.Free  n -> validate =<< synth (tglobal n)
    ST.Bound n -> validate =<< synth (tbound n)
    ST.Type    -> validate =<< synth _Type
    ST.Unit    -> validate =<< synth _Unit
    t ST.:=> b -> validate =<< synth (fmap _check t >~> _check b)
    f ST.:$  a -> validate =<< synth (_synth f .$  _check a)
    a ST.:-> b -> validate =<< synth (_check a --> _check b)
    l ST.:*  r -> validate =<< synth (_check l .*  _check r)
    ST.Ann s b -> local (const s) $ b _K
    where
    _check r = tm <$> Check (r . Just)
    _synth r = Synth (r Nothing)
    validate r@(_T ::: _K') = case _K of
      Just _K -> r <$ unify _K' _K
      _       -> pure r

tglobal :: (C.Type ty, Has (Error P.Print) sig m) => S.TName -> Synth m ty
tglobal (S.TName s) = Synth $ asks (Env.lookup s) >>= \case
  Just b  -> pure (C.tglobal s ::: b)
  Nothing -> freeVariable (pretty s)

tbound :: (C.Type ty, Has (Error P.Print) sig m) => Name -> Synth m ty
tbound n = bound n C.tbound P.tvar

_Type :: (Applicative m, C.Type t) => Synth m t
_Type = Synth $ pure $ C._Type ::: C._Type

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
  :: Algebra sig m
  => (Name ::: Check m Type)
  -> Check m Type
  -> Synth m Type
(n ::: t) >~> b = Synth $ do
  _T <- check (t ::: C._Type)
  ftb' <- n ::: _T |- ((n ::: _T) C.==>) <$> check (b ::: C._Type)
  pure $ ftb' ::: C._Type

infixr 1 >~>


-- Expressions

elabExpr :: (Has (Error P.Print) sig m, Has (Reader Span) sig m, C.Expr expr) => (SE.Expr ::: Maybe Type) -> EnvC m (expr ::: Type)
elabExpr (t ::: _K) = SE.fold alg t _K
  where
  alg t _T = case t of
    SE.Free  n -> validate =<< synth (eglobal n)
    SE.Bound n -> validate =<< synth (ebound n)
    SE.Lam n b -> check (lam n (_check b) ::: _T)
    f SE.:$  a -> validate =<< synth (_synth f $$  _check a)
    l SE.:*  r -> check (_check l **  _check r ::: _T)
    SE.Unit    -> validate =<< synth unit
    SE.Ann s b -> local (const s) $ b _T
    where
    _check r = tm <$> Check (r . Just)
    _synth r = Synth (r Nothing)
    check (m ::: _T) = expectChecked _T >>= \ _T -> (::: _T) <$> runCheck m _T
    validate r@(_ ::: _T') = case _T of
      Just _T -> r <$ unify _T' _T
      _       -> pure r

eglobal :: (C.Expr expr, Has (Error P.Print) sig m) => S.EName -> Synth m expr
eglobal (S.EName s) = Synth $ asks (Env.lookup s) >>= \case
  Just b  -> pure (C.global s ::: b)
  Nothing -> freeVariable (pretty s)

ebound :: (C.Expr expr, Has (Error P.Print) sig m) => Name -> Synth m expr
ebound n = bound n C.bound P.evar

($$) :: (C.Expr expr, Has (Error P.Print) sig m) => Synth m expr -> Check m expr -> Synth m expr
($$) = app (C.$$)

tlam :: (C.Expr expr, Has (Error P.Print) sig m) => Name -> Check m expr -> Check m expr
tlam n b = Check $ \ ty -> do
  (n', _T, _B) <- expectQuantifiedType (fromWords "when checking type lambda") ty
  n' ::: _T |- C.tlam n <$> check (b ::: _B)

lam :: (C.Expr expr, Has (Error P.Print) sig m) => Name -> Check m expr -> Check m expr
lam n b = Check $ \ ty -> do
  (_A, _B) <- expectFunctionType (fromWords "when checking lambda") ty
  n ::: _A |- C.lam n <$> check (b ::: _B)

unit :: (Applicative m, C.Expr t) => Synth m t
unit = Synth . pure $ C.unit ::: C._Unit

(**) :: (C.Expr expr, Has (Error P.Print) sig m) => Check m expr -> Check m expr -> Check m expr
l ** r = Check $ \ _T -> do
  (_L, _R) <- expectProductType (fromWords "when checking product") _T
  l' <- check (l ::: _L)
  r' <- check (r ::: _R)
  pure (l' C.** r')


-- Context

(|-) :: Has (Reader Context) sig m => Name ::: Type -> m a -> m a
n ::: t |- m = local (IntMap.insert (id' n) t) m

infix 1 |-


-- Failures

fromWords :: String -> P.Print
fromWords = fillSep . map pretty . words

err :: Has (Error P.Print) sig m => P.Print -> m a
err = throwError . group

tbd :: Has (Error P.Print) sig m => m a
tbd = err $ pretty "TBD"

mismatch :: Has (Error P.Print) sig m => P.Print -> P.Print -> P.Print -> m a
mismatch msg exp act = err $ msg
  </> pretty "expected:" <+> exp
  </> pretty "  actual:" <+> act

couldNotUnify :: Has (Error P.Print) sig m => Type -> Type -> m a
couldNotUnify t1 t2 = mismatch (fromWords "could not unify") (interpret t2) (interpret t1)

couldNotSynthesize :: Has (Error P.Print) sig m => m a
couldNotSynthesize = err $ fromWords "could not synthesize a type"

freeVariable :: Has (Error P.Print) sig m => P.Print -> m a
freeVariable v = err $ fromWords "variable not in scope:" <+> v


-- Patterns

expectChecked :: Has (Error P.Print) sig m => Maybe Type -> m Type
expectChecked = maybe couldNotSynthesize pure

expectQuantifiedType :: Has (Error P.Print) sig m => P.Print -> Type -> m (Name, Type, Type)
expectQuantifiedType s = \case
  (n ::: _T) :=> _B -> pure (n, _T, _B)
  _T                -> mismatch s (pretty "{_} -> _") (interpret _T)

expectFunctionType :: Has (Error P.Print) sig m => P.Print -> Type -> m (Type, Type)
expectFunctionType s = \case
  _A :-> _B -> pure (_A, _B)
  _T        -> mismatch s (pretty "_ -> _") (interpret _T)

expectProductType :: Has (Error P.Print) sig m => P.Print -> Type -> m (Type, Type)
expectProductType s = \case
  _A :* _B -> pure (_A, _B)
  _T       -> mismatch s (pretty "(_, _)") (interpret _T)
