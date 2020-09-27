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
( Elab(..)
, Check(..)
, Synth(..)
, check
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
import           Control.Effect.Error
import qualified Facet.Core as CT
import qualified Facet.Core.Lifted as C
import qualified Facet.Core.Lifted as CTL
import           Facet.Env
import           Facet.Functor.C
import           Facet.Print (Print, tvar)
import qualified Facet.Surface as S
import           Facet.Syntax
import           Facet.Type
import           Silkscreen

newtype Elab a = Elab { elab :: a }

instance S.ForAll a b => S.ForAll (Elab a) (Elab b) where
  t >=> b = Elab $ elab t S.>=> elab . b . Elab

instance S.Type a => S.Type (Elab a) where
  tglobal = Elab . S.tglobal
  a --> b = Elab $ elab a S.--> elab b
  f .$  a = Elab $ elab f S..$  elab a
  l .*  r = Elab $ elab l S..*  elab r

  _Unit = Elab S._Unit
  _Type = Elab S._Type

instance S.Expr a => S.Expr (Elab a) where
  global = Elab . S.global
  lam0 f = Elab $ S.lam0 (elab . f . Elab)
  lam f = Elab $ S.lam (elab . f . either (Left . Elab) (\ (e, k) -> Right (Elab e, Elab . k . elab)))
  f $$ a = Elab $ elab f S.$$ elab a
  unit = Elab S.unit
  l ** r = Elab $ elab l S.** elab r


newtype Check a = Check { runCheck :: Type -> Synth a }
  deriving (Algebra (Reader Type :+: Error Print), Applicative, Functor, Monad) via ReaderC Type Synth

newtype Synth a = Synth { runSynth :: Either Print a }
  deriving (Algebra (Error Print), Applicative, Functor, Monad)

instance MonadFail Synth where
  fail = throwError @Print . pretty

check :: Check a -> Type -> Synth a
check = runCheck

checking :: (Type -> Synth a) -> Check a
checking = Check

switch :: Synth (a ::: Type) -> Check a
switch s = Check $ \ _T -> do
  a ::: _T' <- s
  a <$ unify' _T _T'

unify' :: Type -> Type -> Synth Type
unify' t1 t2 = t2 <$ go 0 (inst t1) (inst t2) -- NB: unification cannot (currently) result in information increase, so it always suffices to take (arbitrarily) the second operand as the result. Failures escape by throwing an exception, so this will not affect failed results.
  where
  go :: Int -> Type' Print -> Type' Print -> Synth ()
  go n = curry $ \case
    (Type,      Type)      -> pure ()
    (Unit,      Unit)      -> pure ()
    (l1 :* r1,  l2 :* r2)  -> go n l1 l2 *> go n r1 r2
    (f1 :$ a1,  f2 :$ a2)  -> go n f1 f2 *> go n a1 a2
    (a1 :-> b1, a2 :-> b2) -> go n a1 a2 *> go n b1 b2
    (t1 :=> b1, t2 :=> b2) -> go n t1 t2 *> go (n + 1) (b1 (Var (tvar n))) (b2 (Var (tvar n)))
    -- FIXME: build and display a diff of the root types
    -- FIXME: indicate the point in the source which led to this
    -- FIXME: what do we do about the Var case? can we unify only closed types? (presumably not because (:=>) contains an open type which it closes, so we will need to operate under them sometimes.) Eq would work but it’s a tall order.
    -- FIXME: Show discards highlighting &c. how do we render arbitrary types to a Print or Notice? Is there some class for that? Do we just monomorphize it?
    (t1, t2) -> fail $ "could not unify " <> show t1 <> " with " <> show t2


-- Types

-- FIXME: differentiate between typed and untyped types?

_Type :: Applicative env => Synth (env Type ::: Type)
_Type = pure $ CTL._Type ::: CT._Type

_Unit :: Applicative env => Synth (env Type ::: Type)
_Unit = pure $ CTL._Unit ::: CT._Type

(.$) :: Applicative env => Synth (env Type ::: Type) -> Check (env Type) -> Synth (env Type ::: Type)
f .$ a = do
  f' ::: _F <- f
  Just (_A, _B) <- pure $ asFn _F
  a' <- check a _A
  pure $ f' CTL..$ a' ::: CT._Type

infixl 9 .$

(.*) :: Applicative env => Check (env Type) -> Check (env Type) -> Synth (env Type ::: Type)
a .* b = do
  a' <- check a CT._Type
  b' <- check b CT._Type
  pure $ a' CTL..* b' ::: CT._Type

infixl 7 .*

(-->) :: Applicative env => Check (env Type) -> Check (env Type) -> Synth (env Type ::: Type)
a --> b = do
  a' <- check a CT._Type
  b' <- check b CT._Type
  pure $ (a' CTL.--> b') ::: CT._Type

infixr 2 -->

(>=>)
  :: Applicative env
  => Check Type
  -> (forall env' . Applicative env' => Extends env env' -> (env' Type ::: Type) -> Check (env' Type))
  -> Synth (env Type ::: Type)
t >=> b = do
  t' <- check t CT._Type
  x <- pure (pure t') CTL.>=> \ env v -> check (b env (v ::: t')) CT._Type
  pure $ x ::: CT._Type

infixr 1 >=>


-- Expressions

asFn :: Type -> Maybe (Type, Type)
asFn = liftA2 (,) <$> dom <*> cod

dom :: Type -> Maybe Type
dom = traverseTypeMaybe (\case
  _A :-> _B -> C (Just _A)
  _         -> C Nothing)

cod :: Type -> Maybe Type
cod = traverseTypeMaybe (\case
  _A :-> _B -> C (Just _B)
  _         -> C Nothing)

($$) :: C.Expr expr => Synth (expr ::: Type) -> Check expr -> Synth (expr ::: Type)
f $$ a = do
  f' ::: _F <- f
  Just (_A, _B) <- pure $ asFn _F
  a' <- check a _A
  pure $ f' C.$$ a' ::: _B

lam0 :: (C.Expr expr, Applicative env) => (forall env' . Applicative env => C.Extends env env' -> env' (expr ::: Type) -> Check (env' expr)) -> Check (env expr)
lam0 f = checking $ \ t -> case asFn t of
  Just (_A, _B) -> C.lam0 $ \ env v -> check (f env (v .: _A)) _B
  _             -> fail "expected function type in lambda"

-- FIXME: internalize scope into Type & Expr?
