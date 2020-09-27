{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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


newtype Check r a = Check { runCheck :: Type r -> Synth a }
  deriving (Algebra (Reader (Type r) :+: Error Print), Applicative, Functor, Monad) via ReaderC (Type r) Synth

newtype Synth a = Synth { runSynth :: Either Print a }
  deriving (Algebra (Error Print), Applicative, Functor, Monad)

instance MonadFail Synth where
  fail = throwError @Print . pretty

elab :: Synth a -> Either Print a
elab = runSynth

check' :: Check r a -> Type r -> Synth a
check' = runCheck

checking :: (Type r -> Synth a) -> Check r a
checking = Check

switch :: Show r => Synth (a ::: Type r) -> Check r a
switch s = Check $ \ _T -> do
  a ::: _T' <- s
  a <$ unify' _T _T'

unify' :: Show r => Type r -> Type r -> Synth (Type r)
unify' = go
  where
  go :: Show r => Type r -> Type r -> Synth (Type r)
  go = curry $ \case
    (Type, Type) -> pure Type
    (Unit, Unit) -> pure Unit
    (l1 :* r1, l2 :* r2) -> (:*) <$> go l1 l2 <*> go r1 r2
    (f1 :$ a1, f2 :$ a2) -> (:$) <$> go f1 f2 <*> go a1 a2
    (a1 :-> b1, a2 :-> b2) -> (:->) <$> go a1 a2 <*> go b1 b2
    (t1 :=> b1, t2 :=> b2) -> (:=>) <$> go t1 t2 <*> unify' b1 b2
    -- FIXME: build and display a diff of the root types
    -- FIXME: indicate the point in the source which led to this
    -- FIXME: what do we do about the Var case? can we unify only closed types? (presumably not because (:=>) contains an open type which it closes, so we will need to operate under them sometimes.) Eq would work but it’s a tall order.
    -- FIXME: Show discards highlighting &c. how do we render arbitrary types to a Print or Notice? Is there some class for that? Do we just monomorphize it?
    (t1, t2) -> fail $ "could not unify " <> show t1 <> " with " <> show t2


-- Types

-- FIXME: differentiate between typed and untyped types?

_Type :: Synth (Type a ::: Type r)
_Type = pure $ Type ::: Type

_Unit :: Synth (Type a ::: Type r)
_Unit = pure $ Unit ::: Type

(.$) :: Synth (Type r ::: Type r) -> Check r (Type r) -> Synth (Type r ::: Type r)
a .$ b = do
  a' ::: (_A :-> _B) <- a
  b' <- check' b _A
  pure $ a' :$ b' ::: Type

infixl 9 .$

(.*) :: Check r (Type r) -> Check r (Type r) -> Synth (Type r ::: Type r)
a .* b = do
  a' <- check' a Type
  b' <- check' b Type
  pure $ a' :* b' ::: Type

infixl 7 .*

(-->) :: Check r (Type r) -> Check r (Type r) -> Synth (Type r ::: Type r)
a --> b = do
  a' <- check' a Type
  b' <- check' b Type
  pure $ (a' :-> b') ::: Type

infixr 2 -->

(>=>)
  :: Check r (Type r)
  -> ((Type (Maybe r) ::: Type (Maybe r)) -> Check (Maybe r) (Type (Maybe r)))
  -> Synth (Type r ::: Type r)
t >=> b = do
  t' <- check' t Type
  b' <- check' (b (Var Nothing ::: fmap Just t')) Type
  pure $ (t' :=> b')  ::: Type

infixr 1 >=>


-- Expressions

($$) :: C.Expr expr => Synth (expr (a -> b) ::: Type r) -> Check r (expr a) -> Synth (expr b ::: Type r)
f $$ a = do
  f' ::: (_A :-> _B) <- f
  a' <- check' a _A
  pure $ f' C.$$ a' ::: _B

lam0 :: (C.Expr expr, C.Permutable env) => (forall env' . C.Permutable env => C.Extends env env' -> env' (expr a ::: Type r) -> Check r (env' (expr b))) -> Check r (env (expr (a -> b)))
lam0 f = checking $ \case
  _A :-> _B -> C.lam0 $ \ env v -> check' (f env (v .: _A)) _B
  _         -> fail "expected function type in lambda"

-- FIXME: internalize scope into Type & Expr?
