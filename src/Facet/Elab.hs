{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Elab
( check
, synth
, Elab(..)
, Check(..)
, Synth(..)
, elab
, check'
, checking
, switch
, unify'
  -- Types
, _Type
, _Unit
, (.$)
, (.*)
, (-->)
, (>=>)
  -- Expressions
, ($$)
, lam0
) where

import           Control.Algebra
import           Control.Applicative (liftA2)
import           Control.Carrier.Reader
import           Control.Effect.Empty
import           Control.Effect.Error
import qualified Data.Map as Map
import qualified Facet.Core.Lifted as C
import           Facet.Print (Print)
import           Facet.Syntax.Common
import qualified Facet.Syntax.Untyped as U
import           Facet.Type
import           Silkscreen

type Env ty = Map.Map U.Name ty

check :: Elab ty -> ty -> ReaderC (Env ty) Maybe ty
check m = runElab m . Just

synth :: Elab ty -> ReaderC (Env ty) Maybe ty
synth m = runElab m Nothing

newtype Elab ty = Elab { runElab :: Maybe ty -> ReaderC (Env ty) Maybe ty }

instance U.Global (Elab (Type ty)) where
  global n = Elab $ \ ty -> unify ty =<< ReaderC (Map.lookup n)

instance U.ForAll (Elab (Type ty)) (Elab (Type ty)) where
  _A >=> _B = Elab $ \ _T -> do
    _ <- check _A Type
    -- FIXME: this should make a fresh type variable and apply _B to that
    -- FIXME: Type should support type variables I guess
    _ <- check (_B (Elab (const empty))) Type
    unify _T Type

instance U.Type (Elab (Type ty)) where
  _A --> _B = Elab $ \ _T -> do
    _ <- check _A Type
    _ <- check _B Type
    unify _T Type

  _L .* _R = Elab $ \ _T -> do
    _ <- check _L Type
    _ <- check _R Type
    unify _T Type

  (.$) = app

  _Unit = Elab (`unify` Type)
  _Type = Elab (`unify` Type) -- 🕶

-- FIXME: specialize this to Elab (Expr ::: Type)?
instance U.Expr (Elab (Type ty)) where
  lam0 f = Elab $ \case
    Just (_A :-> _B) -> do
      -- FIXME: this should make a fresh type variable of type _A and apply f to that
      -- FIXME: this should extend the local environment
      let b = f (Elab (const empty))
      _ <- check b _B
      pure (_A :-> _B)
    _ -> empty
  lam f = Elab $ \case
    Just (_A :-> _B) -> do
      -- FIXME: this should make a fresh type variable of type _A and apply f to that
      -- FIXME: lam should take a list of clauses, and we should check each one in turn
      -- FIXME: this should extend the local environment
      let b = f (Left (Elab (const empty)))
      _ <- check b _B
      pure (_A :-> _B)
    _ -> empty
  ($$) = app

  unit = Elab (`unify` Unit)
  l ** r = Elab $ \case
    Just (_L :* _R) -> do
      _ <- check l _L
      _ <- check r _R
      pure (_L :* _R)
    _ -> empty

-- FIXME: specialize this to Elab Decl?
instance U.Decl (Elab (Type ty)) (Elab (Type ty)) (Elab (Type ty)) where
  ty .= v = Elab $ \ _T -> do
    _Ty <- check ty Type
    -- FIXME: extend the environment while checking v (for recursive functions)?
    _ <- check v _Ty
    unify _T Type -- FIXME: what should the type of declarations be?

  _A >-> _B = Elab $ \ _T -> do
    _ <- check _A Type
    -- FIXME: this should make a fresh type variable and apply _B to that
    -- FIXME: Type should support type variables I guess
    _ <- check (_B (Elab (const empty))) Type
    unify _T Type

-- FIXME: specialize this to Elab Module?
instance U.Module (Elab (Type ty)) (Elab (Type ty)) (Elab (Type ty)) (Elab (Type ty)) where
  _ .: decl = Elab $ \ _T -> do
    _ <- check decl Type -- FIXME: what should the type of declarations be?
    unify _T Type -- FIXME: what should the type of modules be?

app :: Elab (Type ty) -> Elab (Type ty) -> Elab (Type ty)
f `app` a = Elab $ \ _T -> do
  _F <- synth f
  case _F of
    _A :-> _T' -> do
      _ <- check a _A
      unify _T _T'
    _ -> empty


-- FIXME: handle foralls
unify :: Maybe (Type ty) -> Type ty -> ReaderC (Env (Type ty)) Maybe (Type ty)
unify t1 t2 = maybe pure go t1 t2
  where
  go t1 t2 = case (t1, t2) of
    (Type,      Type)      -> pure Type
    (Unit,      Unit)      -> pure Unit
    (a1 :-> b1, a2 :-> b2) -> (:->) <$> go a1 a2 <*> go b1 b2
    _                      -> empty


newtype Check r a = Check { runCheck :: Type r -> Synth r a }
  deriving (Algebra (Reader (Type r) :+: Reader (Env (Type r)) :+: Error Print), Applicative, Functor, Monad) via ReaderC (Type r) (Synth r)

newtype Synth r a = Synth { runSynth :: Env (Type r) -> Either Print a }
  deriving (Algebra (Reader (Env (Type r)) :+: Error Print), Applicative, Functor, Monad) via ReaderC (Env (Type r)) (Either Print)

instance MonadFail (Synth r) where
  fail = throwError @Print . pretty

elab :: Env (Type r) -> Synth r a -> Either Print a
elab = flip runSynth

check' :: Check r a -> Type r -> Synth r a
check' = runCheck

checking :: (Type r -> Synth r a) -> Check r a
checking = Check

switch :: Synth r (a ::: Type r) -> Check r a
switch s = Check $ \ _T -> do
  a ::: _T' <- s
  a <$ unify' _T _T'

unify' :: Type r -> Type r -> Synth r (Type r)
unify' = go
  where
  go :: Type r -> Type r -> Synth r (Type r)
  go = curry $ \case
    (Type, Type) -> pure C._Type
    (Unit, Unit) -> pure C._Unit
    (l1 :* r1, l2 :* r2) -> (C..*) <$> go l1 l2 <*> go r1 r2
    (f1 :$ a1, f2 :$ a2) -> (C..$) <$> go f1 f2 <*> go a1 a2
    (a1 :-> b1, a2 :-> b2) -> (C.-->) <$> go a1 a2 <*> go b1 b2
    _ -> fail "could not unify"


-- Types

_Type :: Applicative env => Synth r (env (Type r) ::: Type r)
_Type = pure $ pure C._Type ::: Type

_Unit :: Applicative env => Synth r (env (Type r) ::: Type r)
_Unit = pure $ pure C._Unit ::: Type

(.$) :: Applicative env => Synth r (env (Type r) ::: Type r) -> Check r (env (Type r)) -> Synth r (env (Type r) ::: Type r)
a .$ b = do
  a' ::: (_A :-> _B) <- a
  b' <- check' b _A
  pure $ liftA2 (C..$) a' b' ::: Type

infixl 9 .$

(.*) :: Applicative env => Check r (env (Type r)) -> Check r (env (Type r)) -> Synth r (env (Type r) ::: Type r)
a .* b = do
  a' <- check' a Type
  b' <- check' b Type
  pure $ liftA2 (C..*) a' b' ::: Type

infixl 7 .*

(-->) :: Applicative env => Check r (env (Type r)) -> Check r (env (Type r)) -> Synth r (env (Type r) ::: Type r)
a --> b = do
  a' <- check' a Type
  b' <- check' b Type
  pure $ liftA2 (C.-->) a' b' ::: Type

infixr 2 -->

(>=>)
  :: C.Permutable env
  => Check r (Type r) -- FIXME: this is not constructed in any particular scope
  -> (forall env' . C.Permutable env' => C.Extends env env' -> (env' (Type r) ::: Type r) -> Check r (env' (Type r)))
  -> Synth r (env (Type r) ::: Type r)
t >=> b = do
  t' <- check' t Type
  f <- pure (pure t') C.>=> \ env ty -> check' (b env (ty ::: t')) Type
  pure $ f ::: Type

infixr 1 >=>


-- Expressions

($$) :: C.Expr expr => Synth r (expr (a -> b) ::: Type r) -> Check r (expr a) -> Synth r (expr b ::: Type r)
f $$ a = do
  f' ::: (_A :-> _B) <- f
  a' <- check' a _A
  pure $ f' C.$$ a' ::: _B

lam0 :: (C.Expr expr, C.Permutable env) => (forall env' . C.Permutable env => C.Extends env env' -> env' (expr a ::: Type r) -> Check r (env' (expr b))) -> Check r (env (expr (a -> b)))
lam0 f = checking $ \case
  _A :-> _B -> C.lam0 $ \ env v -> check' (f env (v .: _A)) _B
  _         -> fail "expected function type in lambda"

-- FIXME: internalize scope into Type & Expr?
