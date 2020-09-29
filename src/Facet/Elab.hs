{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Elab
( Env
, implicit
, elab
, Elab(..)
, Check(..)
, runSynth
, Synth(..)
, check
, switch
, unify
  -- * General
, global
  -- * Types
, _Type
, _Unit
, (.$)
, (.*)
, (-->)
, (>=>)
  -- * Expressions
, ($$)
, lam0
) where

import           Control.Algebra
import           Control.Carrier.Reader
import           Control.Effect.Error
import           Control.Effect.Parser.Span (Span(..))
import           Control.Monad.Fix
import           Data.Bifunctor (first)
import qualified Data.Map as Map
import qualified Data.Text as T
import qualified Facet.Core.Lifted as C
import           Facet.Name (Scoped)
import           Facet.Print (Print)
import qualified Facet.Surface as S
import           Facet.Syntax
import           Facet.Type
import           Silkscreen (pretty, (<+>), (</>))

type Env = Map.Map T.Text Type

implicit :: Env
implicit = Map.fromList [ (T.pack "Type", C._Type) ]

elab :: (Elab m a ::: Maybe Type) -> m a
elab ~(m ::: t) = runSynth (runElab m t) implicit

newtype Elab m a = Elab { runElab :: Maybe Type -> Synth m a }
  deriving (Algebra (Reader (Maybe Type) :+: Reader Env :+: sig), Applicative, Functor, Monad, MonadFix) via ReaderC (Maybe Type) (Synth m)

checked :: Has (Error Print) sig m => Elab m (a ::: Type) -> Check m a
checked m = Check $ \ _T -> do
  a ::: _T' <- runElab m (Just _T)
  a <$ unify _T _T'

fromCheck :: Has (Error Print) sig m => Check m a -> Elab m (a ::: Type)
fromCheck m = Elab $ \case
  Just t  -> check (m ::: t) .: t
  Nothing -> couldNotSynthesize

synthed :: Elab m a -> Synth m a
synthed (Elab run) = run Nothing

fromSynth :: Has (Error Print) sig m => Synth m (a ::: Type) -> Elab m (a ::: Type)
fromSynth m = Elab $ \case
  Just t  -> check (switch m ::: t) .: t
  Nothing -> m

instance Has (Reader Span) sig m => S.Located (Elab m a) where
  locate = local . const

instance (Has (Error Print) sig m, MonadFix m) => S.Type (Elab m (Type ::: Type)) where
  tglobal = fromSynth . fmap (first C.tglobal) . global . S.getTName
  (n ::: t) >~> b = fromSynth $ (S.getTName n ::: checked t) >~> checked . b . pure
  a --> b = fromSynth $ checked a --> checked b
  f .$  a = fromSynth $ synthed f .$  checked a
  l .*  r = fromSynth $ checked l .*  checked r

  _Unit = fromSynth _Unit
  _Type = fromSynth _Type

instance (C.Expr a, Scoped a, Has (Error Print) sig m, MonadFix m) => S.Expr (Elab m (a ::: Type)) where
  global = fromSynth . fmap (first C.global) . global . S.getEName
  lam0 n f = fromCheck $ lam0 (S.getEName n) (checked . f . pure)
  lam _ _ = tbd
  f $$ a = fromSynth $ synthed f $$ checked a
  unit = tbd
  _ ** _ = tbd


newtype Check m a = Check { runCheck :: Type -> Synth m a }
  deriving (Algebra (Reader Type :+: Reader Env :+: sig), Applicative, Functor, Monad, MonadFix) via ReaderC Type (Synth m)

runSynth :: Synth m a -> Env -> m a
runSynth (Synth m) e = m e

newtype Synth m a = Synth (Env -> m a)
  deriving (Algebra (Reader Env :+: sig), Applicative, Functor, Monad, MonadFix) via ReaderC Env m

check :: (Check m a ::: Type) -> Synth m a
check = uncurryAnn runCheck

switch :: Has (Error Print) sig m => Synth m (a ::: Type) -> Check m a
switch s = Check $ \ _T -> do
  a ::: _T' <- s
  a <$ unify _T _T'

unify :: Has (Error Print) sig m => Type -> Type -> m ()
unify t1 t2 = go t1 t2
  where
  go = curry $ \case
    (Type,      Type)       -> pure ()
    (Unit,      Unit)       -> pure ()
    (l1 :* r1,  l2 :* r2)   -> go l1 l2 *> go r1 r2
    (f1 :$ a1,  f2 :$ a2)
      | f1 == f2
      , Just _ <- goS a1 a2 -> pure ()
    (a1 :-> b1, a2 :-> b2)  -> go a1 a2 *> go b1 b2
    (t1 :=> b1, t2 :=> b2)  -> go (ty t1) (ty t2) *> go b1 b2
    -- FIXME: build and display a diff of the root types
    -- FIXME: indicate the point in the source which led to this
    -- FIXME: Show discards highlighting &c. how do we render arbitrary types to a Print or Notice? Is there some class for that? Do we just monomorphize it?
    (t1, t2) -> couldNotUnify t1 t2
  goS Nil        Nil        = Just (pure ())
  goS (i1 :> l1) (i2 :> l2) = (*>) <$> goS i1 i2 <*> Just (go l1 l2)
  goS _          _          = Nothing


-- General

global :: Has (Error Print) sig m => T.Text -> Synth m (T.Text ::: Type)
global s = asks (Map.lookup s) >>= \case
  Just b  -> pure (s ::: b)
  Nothing -> freeVariable s

app :: Has (Error Print) sig m => (a -> a -> a) -> Synth m (a ::: Type) -> Check m a -> Synth m (a ::: Type)
app ($$) f a = do
  f' ::: _F <- f
  case _F of
    _A :-> _B -> do
      a' <- check (a ::: _A)
      pure $ f' $$ a' ::: _B
    _         -> expectedFunctionType _F (pretty "in application")


-- Types

_Type :: (Applicative m, C.Type t) => Synth m (t ::: Type)
_Type = pure $ C._Type ::: C._Type

_Unit :: (Applicative m, C.Type t) => Synth m (t ::: Type)
_Unit = pure $ C._Unit ::: C._Type

(.$) :: (Has (Error Print) sig m, C.Type t) => Synth m (t ::: Type) -> Check m t -> Synth m (t ::: Type)
(.$) = app (C..$)

infixl 9 .$

(.*) :: (Monad m, C.Type t) => Check m t -> Check m t -> Synth m (t ::: Type)
a .* b = do
  a' <- check (a ::: C._Type)
  b' <- check (b ::: C._Type)
  pure $ a' C..* b' ::: C._Type

infixl 7 .*

(-->) :: (Monad m, C.Type t) => Check m t -> Check m t -> Synth m (t ::: Type)
a --> b = do
  a' <- check (a ::: C._Type)
  b' <- check (b ::: C._Type)
  pure $ (a' C.--> b') ::: C._Type

infixr 2 -->

(>~>)
  :: MonadFix m
  => (T.Text ::: Check m Type)
  -> ((Type ::: Type) -> Check m Type)
  -> Synth m (Type ::: Type)
(n ::: t) >~> b = do
  t' <- check (t ::: C._Type)
  ftb' <- pure (n ::: C.interpret t') C.>=> \ v -> check (b (v ::: t') ::: C._Type)
  pure $ ftb' ::: C._Type

infixr 1 >~>

(>=>)
  :: (MonadFix m, C.Type t, Scoped t)
  => (T.Text ::: Check m Type)
  -> ((t ::: Type) -> Check m t)
  -> Synth m (t ::: Type)
(n ::: t) >=> b = do
  t' <- check (t ::: C._Type)
  ftb' <- pure (n ::: C.interpret t') C.>=> \ v -> check (b (v ::: t') ::: C._Type)
  pure $ ftb' ::: C._Type

infixr 1 >=>


-- Expressions

($$) :: (C.Expr expr, Has (Error Print) sig m) => Synth m (expr ::: Type) -> Check m expr -> Synth m (expr ::: Type)
($$) = app (C.$$)

lam0 :: (C.Expr expr, Scoped expr, Has (Error Print) sig m, MonadFix m) => T.Text -> ((expr ::: Type) -> Check m expr) -> Check m expr
lam0 n f = Check $ \case
  _A :-> _B -> C.lam0 n $ \ v -> check (f (v ::: _A) ::: _B)
  _T        -> expectedFunctionType _T (pretty "when checking lambda")


-- Failures

err :: Has (Error Print) sig m => Print -> m a
err = throwError

tbd :: Has (Error Print) sig m => m a
tbd = err $ pretty "TBD"

couldNotUnify :: Has (Error Print) sig m => Type -> Type -> m a
couldNotUnify t1 t2 = err $ pretty "could not unify" <+> C.interpret t1 <+> pretty "with" <+> C.interpret t2

couldNotSynthesize :: Has (Error Print) sig m => m a
couldNotSynthesize = err $ pretty "could not synthesize a type"

freeVariable :: Has (Error Print) sig m => T.Text -> m a
freeVariable s = err $ pretty "variable not in scope:" <+> pretty s

expectedFunctionType :: Has (Error Print) sig m => Type -> Print -> m a
expectedFunctionType t s = err $ pretty "expected:" <+> pretty "_ -> _" </> pretty "actual:" <+> C.interpret t </> s
