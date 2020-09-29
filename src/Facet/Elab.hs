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
, Synth(..)
, check
, switch
, unify'
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
import           Control.Monad.Fix
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import qualified Data.Text as T
import qualified Facet.Core.Lifted as C
import           Facet.Name (Scoped)
import           Facet.Print (Print)
import qualified Facet.Surface as S
import           Facet.Syntax
import           Facet.Type
import           Silkscreen

type Env e = Map.Map T.Text (e ::: Type)

implicit :: C.Type a => Env a
implicit = Map.fromList [ (T.pack "Type", C._Type ::: C._Type) ]

elab :: C.Type e => (Elab e a ::: Maybe Type) -> Either Print a
elab ~(m ::: t) = runSynth (runElab m t) implicit

newtype Elab e a = Elab { runElab :: Maybe Type -> Synth e a }
  deriving (Algebra (Reader (Maybe Type) :+: Reader (Env e) :+: Error Print), Applicative, Functor, Monad, MonadFail, MonadFix) via ReaderC (Maybe Type) (Synth e)

checked :: Elab e (a ::: Type) -> Check e a
checked (Elab m) = Check (fmap tm . m . Just)

checking :: Check e a -> Elab e (a ::: Type)
checking m = Elab $ \case
  Just t  -> check (m ::: t) .: t
  Nothing -> fail "can’t synthesize a type for this lambda"

synthed :: Elab e a -> Synth e a
synthed (Elab run) = run Nothing

synthing :: Synth e (a ::: Type) -> Elab e (a ::: Type)
synthing m = Elab $ \case
  Just t  -> check (switch m ::: t) .: t
  Nothing -> m

instance S.ForAll (Elab Type (Type ::: Type)) (Elab Type (Type ::: Type)) where
  -- FIXME: something’s amiss here; we don’t check that the bound variable is the correct kind when applying it (or not) for example
  (n ::: t) >=> b = synthing $ (S.getTName n ::: checked t) >=> checked . b . pure

instance S.Type (Elab Type (Type ::: Type)) where
  tglobal = synthing . global . S.getTName
  a --> b = synthing $ checked a --> checked b
  f .$  a = synthing $ synthed f .$  checked a
  l .*  r = synthing $ checked l .*  checked r

  _Unit = synthing _Unit
  _Type = synthing _Type

instance (C.Expr a, Scoped a) => S.Expr (Elab a (a ::: Type)) where
  global = synthing . global . S.getEName
  lam0 n f = checking $ lam0 (S.getEName n) (checked . f . pure)
  lam _ _ = fail "TBD"
  f $$ a = synthing $ synthed f $$ checked a
  unit = fail "TBD"
  _ ** _ = fail "TBD"


newtype Check e a = Check { runCheck :: Type -> Synth e a }
  deriving (Algebra (Reader Type :+: Reader (Env e) :+: Error Print), Applicative, Functor, Monad, MonadFail, MonadFix) via ReaderC Type (Synth e)

newtype Synth e a = Synth { runSynth :: Env e -> Either Print a }
  deriving (Algebra (Reader (Env e) :+: Error Print), Applicative, Functor, Monad, MonadFix) via ReaderC (Env e) (Either Print)

instance MonadFail (Synth e) where
  fail = throwError @Print . pretty

check :: (Check e a ::: Type) -> Synth e a
check = uncurryAnn runCheck

switch :: Synth e (a ::: Type) -> Check e a
switch s = Check $ \ _T -> do
  a ::: _T' <- s
  a <$ unify' _T _T'

unify' :: Type -> Type -> Synth e Type
unify' t1 t2 = t2 <$ go t1 t2 -- NB: unification cannot (currently) result in information increase, so it always suffices to take (arbitrarily) the second operand as the result. Failures escape by throwing an exception, so this will not affect failed results.
  where
  go :: Type -> Type -> Synth e ()
  go = curry $ \case
    (Type,      Type)      -> pure ()
    (Unit,      Unit)      -> pure ()
    (l1 :* r1,  l2 :* r2)  -> go l1 l2 *> go r1 r2
    (f1 :$ a1,  f2 :$ a2)
      | f1 == f2           -> fromMaybe (failWith (f1 :$ a1) (f2 :$ a2)) (goS a1 a2)
    (a1 :-> b1, a2 :-> b2) -> go a1 a2 *> go b1 b2
    (t1 :=> b1, t2 :=> b2) -> go (ty t1) (ty t2) *> go b1 b2
    -- FIXME: build and display a diff of the root types
    -- FIXME: indicate the point in the source which led to this
    -- FIXME: Show discards highlighting &c. how do we render arbitrary types to a Print or Notice? Is there some class for that? Do we just monomorphize it?
    (t1, t2) -> failWith t1 t2
  failWith t1 t2 = fail $ "could not unify " <> show t1 <> " with " <> show t2
  goS Nil        Nil        = Just (pure ())
  goS (i1 :> l1) (i2 :> l2) = (*>) <$> goS i1 i2 <*> Just (go l1 l2)
  goS _          _          = Nothing


-- General

global :: T.Text -> Synth e (e ::: Type)
global s = asks (Map.lookup s) >>= \case
  Just b  -> pure b
  Nothing -> fail $ "variable not in scope: " <> show s

app :: (a -> a -> a) -> Synth e (a ::: Type) -> Check e a -> Synth e (a ::: Type)
app ($$) f a = do
  f' ::: (_A :-> _B) <- f
  a' <- check (a ::: _A)
  pure $ f' $$ a' ::: _B


-- Types

_Type :: Synth e (Type ::: Type)
_Type = pure $ C._Type ::: C._Type

_Unit :: Synth e (Type ::: Type)
_Unit = pure $ C._Unit ::: C._Type

(.$) :: Synth e (Type ::: Type) -> Check e Type -> Synth e (Type ::: Type)
(.$) = app (C..$)

infixl 9 .$

(.*) :: Check e Type -> Check e Type -> Synth e (Type ::: Type)
a .* b = do
  a' <- check (a ::: C._Type)
  b' <- check (b ::: C._Type)
  pure $ a' C..* b' ::: C._Type

infixl 7 .*

(-->) :: Check e Type -> Check e Type -> Synth e (Type ::: Type)
a --> b = do
  a' <- check (a ::: C._Type)
  b' <- check (b ::: C._Type)
  pure $ (a' C.--> b') ::: C._Type

infixr 2 -->

(>=>)
  :: (T.Text ::: Check e Type)
  -> ((Type ::: Type) -> Check e Type)
  -> Synth e (Type ::: Type)
(n ::: t) >=> b = do
  t' <- check (t ::: C._Type)
  ftb' <- pure (n ::: t') C.>=> \ v -> check (b (v ::: t') ::: C._Type)
  pure $ ftb' ::: C._Type

infixr 1 >=>


-- Expressions

($$) :: C.Expr expr => Synth e (expr ::: Type) -> Check e expr -> Synth e (expr ::: Type)
($$) = app (C.$$)

lam0 :: (C.Expr expr, Scoped expr) => T.Text -> ((expr ::: Type) -> Check e expr) -> Check e expr
lam0 n f = Check $ \case
  _A :-> _B -> C.lam0 n $ \ v -> check (f (v ::: _A) ::: _B)
  _         -> fail "expected function type in lambda"
