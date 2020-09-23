{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Elab
( check
, synth
, Elab(..)
) where

import           Control.Carrier.Reader
import           Control.Effect.Empty
import qualified Data.Map as Map
import qualified Facet.Syntax.Untyped as U
import           Facet.Type

type Env = Map.Map U.Name Type

check :: Elab ty -> Type -> ReaderC Env Maybe ty
check m = elab m . Just

synth :: Elab ty -> ReaderC Env Maybe ty
synth m = elab m Nothing

newtype Elab ty = Elab { elab :: Maybe Type -> ReaderC Env Maybe ty }

instance U.Global (Elab Type) where
  global n = Elab $ \ ty -> unify ty =<< ReaderC (Map.lookup n)

instance U.ForAll (Elab Type) (Elab Type) where
  _A >=> _B = Elab $ \ _T -> do
    _ <- check _A Type
    -- FIXME: this should make a fresh type variable and apply _B to that
    -- FIXME: Type should support type variables I guess
    _ <- check (_B (Elab (const empty))) Type
    unify _T Type

instance U.Type (Elab Type) where
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
instance U.Expr (Elab Type) where
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
instance U.Decl (Elab Type) (Elab Type) (Elab Type) where
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
instance U.Module (Elab Type) (Elab Type) (Elab Type) (Elab Type) where
  _ .: decl = Elab $ \ _T -> do
    _ <- check decl Type -- FIXME: what should the type of declarations be?
    unify _T Type -- FIXME: what should the type of modules be?

app :: Elab Type -> Elab Type -> Elab Type
f `app` a = Elab $ \ _T -> do
  _F <- synth f
  case _F of
    _A :-> _T' -> do
      _ <- check a _A
      unify _T _T'
    _ -> empty


-- FIXME: handle foralls
unify :: Maybe Type -> Type -> ReaderC Env Maybe Type
unify t1 t2 = maybe pure go t1 t2
  where
  go t1 t2 = case (t1, t2) of
    (Type,      Type)      -> pure Type
    (a1 :-> b1, a2 :-> b2) -> (:->) <$> go a1 a2 <*> go b1 b2
    _                      -> empty
