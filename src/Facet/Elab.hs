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
import qualified Control.Carrier.Error.Church as E
import           Control.Carrier.Reader
import           Control.Effect.Error
import           Control.Effect.Parser.Span (Pos(..), Span(..))
import           Control.Monad.Fix
import qualified Data.Map as Map
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
elab ~(m ::: t) = runSynth (runElab m t) (Span (Pos 0 0) (Pos 0 0)) implicit

newtype Elab e a = Elab { runElab :: Maybe Type -> Synth e a }
  deriving (Algebra (Reader (Maybe Type) :+: Reader Span :+: Reader (Env e) :+: Error Print), Applicative, Functor, Monad, MonadFail, MonadFix) via ReaderC (Maybe Type) (Synth e)

checked :: Elab e (a ::: Type) -> Check e a
checked m = Check $ \ _T -> do
  a ::: _T' <- runElab m (Just _T)
  a <$ unify _T _T'

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

instance S.Located (Elab e a) where
  locate _ = id

instance S.ForAll (Elab Type (Type ::: Type)) (Elab Type (Type ::: Type)) where
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
  deriving (Algebra (Reader Type :+: Reader Span :+: Reader (Env e) :+: Error Print), Applicative, Functor, Monad, MonadFail, MonadFix) via ReaderC Type (Synth e)

newtype Synth e a = Synth { runSynth :: Span -> Env e -> Either Print a }
  deriving (Algebra (Reader Span :+: Reader (Env e) :+: Error Print), Applicative, Functor, Monad, MonadFix) via ReaderC Span (ReaderC (Env e) (Either Print))

instance MonadFail (Synth e) where
  fail = throwError @Print . pretty

check :: (Check e a ::: Type) -> Synth e a
check = uncurryAnn runCheck

switch :: Synth e (a ::: Type) -> Check e a
switch s = Check $ \ _T -> do
  a ::: _T' <- s
  a <$ unify _T _T'

unify :: Type -> Type -> Synth e Type
unify t1 t2 = t2 <$ go t1 t2 -- NB: unification cannot (currently) result in information increase, so it always suffices to take (arbitrarily) the second operand as the result. Failures escape by throwing an exception, so this will not affect failed results.
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
  f' ::: _F <- f
  case _F of
    _A :-> _B -> do
      a' <- check (a ::: _A)
      pure $ f' $$ a' ::: _B
    _         -> fail $ "cannot apply value of non-function type " <> show _F


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


-- Contextualized errors

newtype ErrorC e m a = ErrorC { runErrorC :: E.ErrorC (Span, e) m a }
  deriving (Applicative, Functor, Monad)

instance Has (Reader Span) sig m => Algebra (Error e :+: sig) (ErrorC e m) where
  alg hdl sig ctx = ErrorC $ case sig of
    L (L (Throw e))   -> ask @Span >>= throwError . flip (,) e
    L (R (Catch m h)) -> runErrorC (hdl (m <$ ctx)) `catchError` (runErrorC . hdl . (<$ ctx) . h . snd @Span)
    R other           -> alg (runErrorC . hdl) (R other) ctx
