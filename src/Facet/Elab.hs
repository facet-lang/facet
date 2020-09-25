{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Elab
( check
, synth
, Elab(..)
, Check(..)
, Synth(..)
, check'
, checking
, switch
, unify'
  -- Types
, _Type
  -- Expressions
, ($$)
, lam0
) where

import           Control.Carrier.Reader
import           Control.Effect.Empty
import           Control.Effect.Sum ((:+:))
import qualified Data.Map as Map
import qualified Facet.Core.Lifted as C
import           Facet.Syntax.Common
import qualified Facet.Syntax.Untyped as U
import           Facet.Type

type Env ty = Map.Map U.Name ty

check :: Elab ty -> ty -> ReaderC (Env ty) Maybe ty
check m = elab m . Just

synth :: Elab ty -> ReaderC (Env ty) Maybe ty
synth m = elab m Nothing

newtype Elab ty = Elab { elab :: Maybe ty -> ReaderC (Env ty) Maybe ty }

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


newtype Check ty a = Check { runCheck :: ReaderC (Type ty) (Synth ty) a }
  deriving (Algebra (Reader (Type ty) :+: Reader (Env (Type ty)) :+: Empty), Applicative, Functor, Monad)

newtype Synth ty a = Synth { runSynth :: ReaderC (Env (Type ty)) Maybe a }
  deriving (Algebra (Reader (Env (Type ty)) :+: Empty), Applicative, Functor, Monad)

instance MonadFail (Synth ty) where fail _ = Synth empty

check' :: Check ty a -> Type ty -> Synth ty a
check' c t = runReader t (runCheck c)

checking :: (Type ty -> Synth ty a) -> Check ty a
checking = Check . ReaderC

switch :: Synth ty (Type ty) -> Check ty (Type ty)
switch s = Check $ ReaderC $ \ _T -> s >>= unify' _T

unify' :: Type ty -> Type ty -> Synth ty (Type ty)
unify' = fmap C.strengthen . go
  where
  go :: Applicative env => Type ty -> Type ty -> Synth ty (env (Type ty))
  go = curry $ \case
    (Type, Type) -> C._Type
    (Unit, Unit) -> C._Unit
    (l1 :* r1, l2 :* r2) -> go l1 l2 C..* go r1 r2
    (f1 :$ a1, f2 :$ a2) -> go f1 f2 C..$ go a1 a2
    (a1 :-> b1, a2 :-> b2) -> go a1 a2 C.--> go b1 b2
    _ -> empty


-- Types

_Type :: (C.Type ty, Applicative env) => Synth ty (env (ty ::: Type ty))
_Type = fmap (::: Type) <$> C._Type


-- Expressions

($$) :: C.Expr expr => Synth ty (expr ::: Type ty) -> Check ty (expr ::: Type ty) -> Synth ty (expr ::: Type ty)
f $$ a = do
  f' ::: (_A :-> _B) <- f
  a' ::: _A <- check' a _A
  pure $ f' C.$$ a' ::: _B

lam0 :: (C.Expr expr, Applicative env) => (forall env' . C.Extends env env' -> env' (expr ::: Type ty) -> Check ty (env' expr)) -> Check ty (env (expr ::: Type ty))
lam0 f = checking $ \case
  _A :-> _B -> do
    f' <- C.lam0 $ \ env ty -> check' (f env (ty .: _A)) _B
    pure $ f' .: (_A :-> _B)
  _ -> empty

-- FIXME: internalize scope into Type & Expr?
