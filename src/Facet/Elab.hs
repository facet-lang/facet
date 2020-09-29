{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
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
import qualified Data.Map as Map
import qualified Data.Text as T
import qualified Facet.Core.Lifted as C
import           Facet.Name (Scoped)
import           Facet.Print (Print)
import qualified Facet.Surface as S
import           Facet.Syntax
import           Facet.Type
import           Silkscreen (pretty, (<+>), (</>))

type Env e = Map.Map T.Text (e ::: Type)

implicit :: C.Type a => Env a
implicit = Map.fromList [ (T.pack "Type", C._Type ::: C._Type) ]

elab :: C.Type e => (Elab e m a ::: Maybe Type) -> m a
elab ~(m ::: t) = runSynth (runElab m t) implicit

newtype Elab e m a = Elab { runElab :: Maybe Type -> Synth e m a }
  deriving (Algebra (Reader (Maybe Type) :+: Reader (Env e) :+: sig), Applicative, Functor, Monad, MonadFail, MonadFix) via ReaderC (Maybe Type) (Synth e m)

checked :: Has (Error Print) sig m => Elab e m (a ::: Type) -> Check e m a
checked m = Check $ \ _T -> do
  a ::: _T' <- runElab m (Just _T)
  a <$ unify _T _T'

checking :: Has (Error Print) sig m => Check e m a -> Elab e m (a ::: Type)
checking m = Elab $ \case
  Just t  -> check (m ::: t) .: t
  Nothing -> couldNotSynthesize

synthed :: Elab e m a -> Synth e m a
synthed (Elab run) = run Nothing

synthing :: Has (Error Print) sig m => Synth e m (a ::: Type) -> Elab e m (a ::: Type)
synthing m = Elab $ \case
  Just t  -> check (switch m ::: t) .: t
  Nothing -> m

instance Has (Reader Span) sig m => S.Located (Elab e m a) where
  locate = local . const

instance (Has (Error Print) sig m, MonadFix m) => S.ForAll (Elab Type m (Type ::: Type)) (Elab Type m (Type ::: Type)) where
  (n ::: t) >=> b = synthing $ (S.getTName n ::: checked t) >=> checked . b . pure

instance (Has (Error Print) sig m, MonadFix m) => S.Type (Elab Type m (Type ::: Type)) where
  tglobal = synthing . global . S.getTName
  a --> b = synthing $ checked a --> checked b
  f .$  a = synthing $ synthed f .$  checked a
  l .*  r = synthing $ checked l .*  checked r

  _Unit = synthing _Unit
  _Type = synthing _Type

instance (C.Expr a, Scoped a, Has (Error Print) sig m, MonadFix m) => S.Expr (Elab a m (a ::: Type)) where
  global = synthing . global . S.getEName
  lam0 n f = checking $ lam0 (S.getEName n) (checked . f . pure)
  lam _ _ = tbd
  f $$ a = synthing $ synthed f $$ checked a
  unit = tbd
  _ ** _ = tbd


newtype Check e m a = Check { runCheck :: Type -> Synth e m a }
  deriving (Algebra (Reader Type :+: Reader (Env e) :+: sig), Applicative, Functor, Monad, MonadFail, MonadFix) via ReaderC Type (Synth e m)

runSynth :: Synth e m a -> Env e -> m a
runSynth (Synth m) e = m e

newtype Synth e m a = Synth (Env e -> m a)
  deriving (Algebra (Reader (Env e) :+: sig), Applicative, Functor, Monad, MonadFail, MonadFix) via ReaderC (Env e) m

check :: (Check e m a ::: Type) -> Synth e m a
check = uncurryAnn runCheck

switch :: Has (Error Print) sig m => Synth e m (a ::: Type) -> Check e m a
switch s = Check $ \ _T -> do
  a ::: _T' <- s
  a <$ unify _T _T'

unify :: Has (Error Print) sig m => Type -> Type -> Synth e m ()
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

global :: Has (Error Print) sig m => T.Text -> Synth e m (e ::: Type)
global s = asks (Map.lookup s) >>= \case
  Just b  -> pure b
  Nothing -> freeVariable s

app :: Has (Error Print) sig m => (a -> a -> a) -> Synth e m (a ::: Type) -> Check e m a -> Synth e m (a ::: Type)
app ($$) f a = do
  f' ::: _F <- f
  case _F of
    _A :-> _B -> do
      a' <- check (a ::: _A)
      pure $ f' $$ a' ::: _B
    _         -> expectedFunctionType _F (pretty "in application")


-- Types

_Type :: Applicative m => Synth e m (Type ::: Type)
_Type = pure $ C._Type ::: C._Type

_Unit :: Applicative m => Synth e m (Type ::: Type)
_Unit = pure $ C._Unit ::: C._Type

(.$) :: Has (Error Print) sig m => Synth e m (Type ::: Type) -> Check e m Type -> Synth e m (Type ::: Type)
(.$) = app (C..$)

infixl 9 .$

(.*) :: Monad m => Check e m Type -> Check e m Type -> Synth e m (Type ::: Type)
a .* b = do
  a' <- check (a ::: C._Type)
  b' <- check (b ::: C._Type)
  pure $ a' C..* b' ::: C._Type

infixl 7 .*

(-->) :: Monad m => Check e m Type -> Check e m Type -> Synth e m (Type ::: Type)
a --> b = do
  a' <- check (a ::: C._Type)
  b' <- check (b ::: C._Type)
  pure $ (a' C.--> b') ::: C._Type

infixr 2 -->

(>=>)
  :: MonadFix m
  => (T.Text ::: Check e m Type)
  -> ((Type ::: Type) -> Check e m Type)
  -> Synth e m (Type ::: Type)
(n ::: t) >=> b = do
  t' <- check (t ::: C._Type)
  ftb' <- pure (n ::: t') C.>=> \ v -> check (b (v ::: t') ::: C._Type)
  pure $ ftb' ::: C._Type

infixr 1 >=>


-- Expressions

($$) :: (C.Expr expr, Has (Error Print) sig m) => Synth e m (expr ::: Type) -> Check e m expr -> Synth e m (expr ::: Type)
($$) = app (C.$$)

lam0 :: (C.Expr expr, Scoped expr, Has (Error Print) sig m, MonadFix m) => T.Text -> ((expr ::: Type) -> Check e m expr) -> Check e m expr
lam0 n f = Check $ \case
  _A :-> _B -> C.lam0 n $ \ v -> check (f (v ::: _A) ::: _B)
  _T        -> expectedFunctionType _T (pretty "when checking lambda")


-- Failures

err :: Has (Error Print) sig m => Print -> m a
err = throwError

tbd :: Has (Error Print) sig m => m a
tbd = err $ pretty "TBD"

couldNotUnify :: Has (Error Print) sig m => Type -> Type -> m a
couldNotUnify t1 t2 = err $ pretty "could not unify " <+> C.interpret t1 <+> pretty " with " <+> C.interpret t2

couldNotSynthesize :: Has (Error Print) sig m => m a
couldNotSynthesize = err $ pretty "could not synthesize a type"

freeVariable :: Has (Error Print) sig m => T.Text -> m a
freeVariable s = err $ pretty "variable not in scope:" <+> pretty s

expectedFunctionType :: Has (Error Print) sig m => Type -> Print -> m a
expectedFunctionType t s = err $ pretty "expected:" <+> pretty "_ -> _" </> pretty "actual:" <+> C.interpret t </> s
