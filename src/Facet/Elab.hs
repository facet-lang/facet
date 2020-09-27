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
import qualified Data.Kind as K
import qualified Data.Map as Map
import qualified Facet.Core.Lifted as C
import           Facet.Functor.C ((:.:)(C))
import           Facet.Print (Print, tvar)
import           Facet.Syntax.Common
import qualified Facet.Syntax.Untyped as U
import           Facet.Type
import qualified Facet.Type.Typed as T
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


newtype Check a = Check { runCheck :: ForAll (T.Type K.Type) -> Synth a }
  deriving (Algebra (Reader (ForAll (T.Type K.Type)) :+: Error Print), Applicative, Functor, Monad) via ReaderC (ForAll (T.Type K.Type)) Synth

newtype Synth a = Synth { runSynth :: Either Print a }
  deriving (Algebra (Error Print), Applicative, Functor, Monad)

instance MonadFail Synth where
  fail = throwError @Print . pretty

elab :: Synth a -> Either Print a
elab = runSynth

check' :: Check a -> ForAll (T.Type K.Type) -> Synth a
check' = runCheck

checking :: (ForAll (T.Type K.Type) -> Synth a) -> Check a
checking = Check

switch :: Synth (a ::: ForAll (T.Type K.Type)) -> Check a
switch s = Check $ \ _T -> do
  a ::: _T' <- s
  a <$ unify' _T _T'

unify' :: ForAll (T.Type K.Type) -> ForAll (T.Type K.Type) -> Synth (ForAll (T.Type K.Type))
unify' t1 t2 = t2 <$ go 0 (instantiate t1) (instantiate t2) -- NB: unification cannot (currently) result in information increase, so it always suffices to take (arbitrarily) the second operand as the result. Failures escape by throwing an exception, so this will not affect failed results.
  where
  go :: Int -> T.Type k1 Print -> T.Type k2 Print -> Synth ()
  go n = curry $ \case
    (T.Type, T.Type) -> pure ()
    (T.Unit, T.Unit) -> pure ()
    (l1 T.:* r1, l2 T.:* r2) -> go n l1 l2 *> go n r1 r2
    (f1 T.:$ a1, f2 T.:$ a2) -> go n f1 f2 *> go n a1 a2
    (a1 T.:-> b1, a2 T.:-> b2) -> go n a1 a2 *> go n b1 b2
    (t1 T.:=> b1, t2 T.:=> b2) -> go n t1 t2 *> go (n + 1) (b1 (T.Var (tvar n))) (b2 (T.Var (tvar n)))
    -- FIXME: build and display a diff of the root types
    -- FIXME: indicate the point in the source which led to this
    -- FIXME: what do we do about the Var case? can we unify only closed types? (presumably not because (:=>) contains an open type which it closes, so we will need to operate under them sometimes.) Eq would work but it’s a tall order.
    -- FIXME: Show discards highlighting &c. how do we render arbitrary types to a Print or Notice? Is there some class for that? Do we just monomorphize it?
    (t1, t2) -> fail $ "could not unify " <> show t1 <> " with " <> show t2


-- Types

-- FIXME: differentiate between typed and untyped types?

_Type :: Synth (ForAll (T.Type K.Type) ::: ForAll (T.Type K.Type))
_Type = pure $ Abstract T.Type ::: Abstract T.Type

_Unit :: Synth (ForAll (T.Type K.Type) ::: ForAll (T.Type K.Type))
_Unit = pure $ Abstract T.Unit ::: Abstract T.Type

(.$) :: Synth (ForAll (T.Type (k1 -> k2)) ::: ForAll (T.Type K.Type)) -> Check (ForAll (T.Type k1)) -> Synth (ForAll (T.Type k2) ::: ForAll (T.Type K.Type))
f .$ a = do
  f' ::: _F <- f
  Just (_A, _B) <- pure $ asFn _F
  a' <- check' a _A
  pure $ Abstract (instantiate f' T.:$ instantiate a') ::: Abstract T.Type

infixl 9 .$

(.*) :: Check (ForAll (T.Type K.Type)) -> Check (ForAll (T.Type K.Type)) -> Synth (ForAll (T.Type K.Type) ::: ForAll (T.Type K.Type))
a .* b = do
  a' <- check' a (Abstract T.Type)
  b' <- check' b (Abstract T.Type)
  pure $ Abstract (instantiate a' T.:* instantiate b') ::: Abstract T.Type

infixl 7 .*

(-->) :: Check (ForAll (T.Type K.Type)) -> Check (ForAll (T.Type K.Type)) -> Synth (ForAll (T.Type K.Type) ::: ForAll (T.Type K.Type))
a --> b = do
  a' <- check' a (Abstract T.Type)
  b' <- check' b (Abstract T.Type)
  pure $ Abstract (instantiate a' T.:-> instantiate b') ::: Abstract T.Type

infixr 2 -->

(>=>)
  :: Check (Type r)
  -> ((Type (Maybe r) ::: Type (Maybe r)) -> Check (Type (Maybe r)))
  -> Synth (Type r ::: Type r)
t >=> b = do
  t' <- check' t (Abstract T.Type)
  b' <- check' (b (Var Nothing ::: fmap Just t')) (Abstract T.Type)
  pure $ (t' :=> b')  ::: Type

infixr 1 >=>


-- Expressions

asFn :: ForAll (T.Type K.Type) -> Maybe (ForAll (T.Type K.Type), ForAll (T.Type K.Type))
asFn = liftA2 (,) <$> dom <*> cod

dom :: ForAll (T.Type K.Type) -> Maybe (ForAll (T.Type K.Type))
dom = sequenceForAllMaybe . hoistForAll (\case
  _A T.:-> _B -> C (Just _A)
  _           -> C Nothing)

cod :: ForAll (T.Type K.Type) -> Maybe (ForAll (T.Type K.Type))
cod = sequenceForAllMaybe . hoistForAll (\case
  _A T.:-> _B -> C (Just _B)
  _           -> C Nothing)

($$) :: C.Expr expr => Synth (expr (a -> b) ::: ForAll (T.Type K.Type)) -> Check (expr a) -> Synth (expr b ::: ForAll (T.Type K.Type))
f $$ a = do
  f' ::: _F <- f
  Just (_A, _B) <- pure $ asFn _F
  a' <- check' a _A
  pure $ f' C.$$ a' ::: _B

lam0 :: (C.Expr expr, C.Permutable env) => (forall env' . C.Permutable env => C.Extends env env' -> env' (expr a ::: ForAll (T.Type K.Type)) -> Check (env' (expr b))) -> Check (env (expr (a -> b)))
lam0 f = checking $ \ t -> case asFn t of
  Just (_A, _B) -> C.lam0 $ \ env v -> check' (f env (v .: _A)) _B
  _             -> fail "expected function type in lambda"

-- FIXME: internalize scope into Type & Expr?
