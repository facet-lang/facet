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
, elab
, Elab(..)
, Check(..)
, Synth(..)
, check
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
import           Control.Monad.Fix
import qualified Data.Map as Map
import           Data.Text (Text)
import qualified Facet.Core as CT
import qualified Facet.Core.Lifted as C
import           Facet.Functor.C
import           Facet.Name (Scoped)
import           Facet.Print (Print)
import qualified Facet.Surface as S
import           Facet.Syntax
import           Facet.Type
import           Silkscreen

type Env = Map.Map Text Type

elab :: (Elab a ::: Maybe Type) -> Either Print a
elab ~(m ::: t) = runSynth (runElab m mempty t)

newtype Elab a = Elab { runElab :: Env -> Maybe Type -> Synth a }
  deriving (Algebra (Reader Env :+: Reader (Maybe Type) :+: Error Print), Applicative, Functor, Monad, MonadFail, MonadFix) via ReaderC Env (ReaderC (Maybe Type) Synth)

checked :: Elab (a ::: Type) -> Check a
checked (Elab m) = Check (fmap tm . m mempty . Just)

checking :: Check a -> Elab (a ::: Type)
checking m = Elab $ const $ \case
  Just t  -> check (m ::: t) .: t
  Nothing -> fail "can’t synthesize a type for this lambda"

synthed :: Elab a -> Synth a
synthed (Elab run) = run mempty Nothing

synthing :: Synth (a ::: Type) -> Elab (a ::: Type)
synthing m = Elab $ const $ \case
  Just t  -> check (switch m ::: t) .: t
  Nothing -> m

instance S.ForAll (Elab (Type ::: Type)) (Elab (Type ::: Type)) where
  (n ::: t) >=> b = synthing $ (S.getTName n ::: checked t) >=> checked . b . pure

instance S.Type (Elab (Type ::: Type)) where
  tglobal s = fail $ "TBD: tglobal " <> show s -- FIXME: carry around a global environment
  a --> b = synthing $ checked a --> checked b
  f .$  a = synthing $ synthed f .$  checked a
  l .*  r = synthing $ checked l .*  checked r

  _Unit = synthing _Unit
  _Type = synthing _Type

instance (C.Expr a, Scoped a) => S.Expr (Elab (a ::: Type)) where
  global s = fail $ "TBD: global " <> show s -- FIXME: carry around a global environment
  lam0 n f = checking $ lam0 (S.getEName n) (checked . f . pure)
  lam _ _ = fail "TBD"
  f $$ a = synthing $ synthed f $$ checked a
  unit = fail "TBD"
  _ ** _ = fail "TBD"


newtype Check a = Check { runCheck :: Type -> Synth a }
  deriving (Algebra (Reader Type :+: Error Print), Applicative, Functor, Monad, MonadFail, MonadFix) via ReaderC Type Synth

newtype Synth a = Synth { runSynth :: Either Print a }
  deriving (Algebra (Error Print), Applicative, Functor, Monad, MonadFix) via Either Print

instance MonadFail Synth where
  fail = throwError @Print . pretty

check :: (Check a ::: Type) -> Synth a
check = uncurryAnn runCheck

switch :: Synth (a ::: Type) -> Check a
switch s = Check $ \ _T -> do
  a ::: _T' <- s
  a <$ unify' _T _T'

unify' :: Type -> Type -> Synth Type
unify' t1 t2 = t2 <$ go (inst t1) (inst t2) -- NB: unification cannot (currently) result in information increase, so it always suffices to take (arbitrarily) the second operand as the result. Failures escape by throwing an exception, so this will not affect failed results.
  where
  go :: Type' Print -> Type' Print -> Synth ()
  go = curry $ \case
    (Bound n1,  Bound n2)
      | n1 == n2           -> pure ()
    (Type,      Type)      -> pure ()
    (Unit,      Unit)      -> pure ()
    (l1 :* r1,  l2 :* r2)  -> go l1 l2 *> go r1 r2
    (f1 :$ a1,  f2 :$ a2)  -> go f1 f2 *> go a1 a2
    (a1 :-> b1, a2 :-> b2) -> go a1 a2 *> go b1 b2
    (t1 :=> b1, t2 :=> b2) -> go (ty t1) (ty t2) *> go b1 b2
    -- FIXME: build and display a diff of the root types
    -- FIXME: indicate the point in the source which led to this
    -- FIXME: what do we do about the Var case? can we unify only closed types? (presumably not because (:=>) contains an open type which it closes, so we will need to operate under them sometimes.) Eq would work but it’s a tall order.
    -- FIXME: Show discards highlighting &c. how do we render arbitrary types to a Print or Notice? Is there some class for that? Do we just monomorphize it?
    (t1, t2) -> fail $ "could not unify " <> show t1 <> " with " <> show t2


-- Types

_Type :: Synth (Type ::: Type)
_Type = pure $ CT._Type ::: CT._Type

_Unit :: Synth (Type ::: Type)
_Unit = pure $ CT._Unit ::: CT._Type

(.$) :: Synth (Type ::: Type) -> Check Type -> Synth (Type ::: Type)
f .$ a = do
  f' ::: _F <- f
  Just (_A, _B) <- pure $ asFn _F
  a' <- check (a ::: _A)
  pure $ f' CT..$ a' ::: CT._Type

infixl 9 .$

(.*) :: Check Type -> Check Type -> Synth (Type ::: Type)
a .* b = do
  a' <- check (a ::: CT._Type)
  b' <- check (b ::: CT._Type)
  pure $ a' CT..* b' ::: CT._Type

infixl 7 .*

(-->) :: Check Type -> Check Type -> Synth (Type ::: Type)
a --> b = do
  a' <- check (a ::: CT._Type)
  b' <- check (b ::: CT._Type)
  pure $ (a' CT.--> b') ::: CT._Type

infixr 2 -->

(>=>)
  :: (Text ::: Check Type)
  -> ((Type ::: Type) -> Check Type)
  -> Synth (Type ::: Type)
(n ::: t) >=> b = do
  t' <- check (t ::: CT._Type)
  ftb' <- pure (n ::: t') C.>=> \ v -> check (b (v ::: t') ::: CT._Type)
  pure $ ftb' ::: CT._Type

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
  a' <- check (a ::: _A)
  pure $ f' C.$$ a' ::: _B

lam0 :: (C.Expr expr, Scoped expr) => Text -> ((expr ::: Type) -> Check expr) -> Check expr
lam0 n f = Check $ \ t -> case asFn t of
  Just (_A, _B) -> C.lam0 n $ \ v -> check (f (v ::: _A) ::: _B)
  _             -> fail "expected function type in lambda"

-- FIXME: internalize scope into Type & Expr?
