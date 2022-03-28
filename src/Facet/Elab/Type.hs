{-# LANGUAGE OverloadedStrings #-}
module Facet.Elab.Type
( -- * Types
  tvar
, Facet.Elab.Type._String
, forAll
, synthType
  -- * Judgements
, switch
) where

import           Control.Algebra
import           Control.Applicative (liftA2)
import           Control.Effect.Reader
import           Control.Effect.Throw
import           Control.Monad (unless)
import           Data.Foldable (foldl')
import           Facet.Elab
import           Facet.Functor.Check
import           Facet.Functor.Synth
import           Facet.Graph (Graph)
import           Facet.Interface
import           Facet.Kind
import           Facet.Lens (views)
import           Facet.Module
import           Facet.Name
import           Facet.Semiring (Few(..), one, zero)
import           Facet.Snoc
import qualified Facet.Surface.Type.Expr as S
import           Facet.Syntax as S hiding (context_)
import qualified Facet.Type.Expr as TX

tvar :: (Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (Throw ErrReason) sig m) => QName -> Elab m (TX.Type :==> Kind)
tvar n = views context_ (lookupInContext n) >>= \case
  [(n', Left _K)] -> pure (TX.Var (Free (Right n')) :==> _K)
  _               -> resolveQ n >>= \case
    q :=: DSubmodule _ _K -> pure $ TX.Var (Global q) :==> _K
    _                     -> freeVariable n

ivar :: (Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (Throw ErrReason) sig m) => QName -> Elab m (RName :==> Kind)
ivar n = resolveQ n >>= \case
    q :=: DSubmodule (SInterface _) _K -> pure $ q :==> _K
    _                                  -> freeVariable n


_String :: Applicative m => m (TX.Type :==> Kind)
_String = pure $ TX.String :==> KType


forAll :: Has (Throw ErrReason) sig m => Name ::: Kind -> Elab m (TX.Type :==> Kind) -> Elab m (TX.Type :==> Kind)
forAll (n ::: t) b = do
  b' <- n :==> t ||- switch b <==: KType
  pure $ TX.ForAll n t b' :==> KType

arrow :: Has (Throw ErrReason) sig m => (a -> b -> c) -> Elab m (a :==> Kind) -> Elab m (b :==> Kind) -> Elab m (c :==> Kind)
arrow mk a b = do
  a' <- switch a <==: KType
  b' <- switch b <==: KType
  pure $ mk a' b' :==> KType


app :: Has (Throw ErrReason) sig m => (a -> b -> c) -> Elab m (a :==> Kind) -> Elab m (b :==> Kind) -> Elab m (c :==> Kind)
app mk f a = do
  f' :==> _F <- f
  (_, _A, _B) <- assertTypeConstructor _F
  -- FIXME: assert that the usage is zero
  a' <- switch a <==: _A
  pure $ mk f' a' :==> _B


comp :: Has (Throw ErrReason) sig m => [Elab m (Interface TX.Type :==> Kind)] -> Elab m (TX.Type :==> Kind) -> Elab m (TX.Type :==> Kind)
comp s t = do
  s' <- traverse ((<==: KInterface) . switch) s
  -- FIXME: polarize types and check that this is a value type being returned
  t' <- switch t <==: KType
  pure $ TX.Comp (fromInterfaces s') t' :==> KType


synthType :: (Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (Throw ErrReason) sig m) => S.Ann S.Type -> Elab m (TX.Type :==> Kind)
synthType (S.Ann s _ e) = pushSpan s $ case e of
  S.TVar n          -> tvar n
  S.TString         -> Facet.Elab.Type._String
  S.TForAll n t b   -> forAll (n ::: t) (synthType b)
  S.TArrow  n q a b -> arrow (TX.Arrow n (maybe Many interpretMul q)) (synthType a) (synthType b)
  S.TComp s t       -> comp (map synthInterface s) (synthType t)
  S.TApp f a        -> app TX.App (synthType f) (synthType a)
  where
  interpretMul = \case
    S.Zero -> zero
    S.One  -> one

synthInterface :: (Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (Throw ErrReason) sig m) => S.Ann (S.Interface (S.Ann S.Type)) -> Elab m (Interface TX.Type :==> Kind)
synthInterface (S.Ann s _ (S.Interface h sp)) = pushSpan s $ do
  -- FIXME: check that the application actually result in an Interface
  h' :==> _ <- ivar h
  sp' <- foldl' (liftA2 (:>)) (pure Nil) ((<==: KType) . switch . synthType <$> sp)
  pure $ Interface h' sp' :==> KInterface


-- Assertions

assertTypeConstructor :: Has (Throw ErrReason) sig m => Kind -> Elab m (Maybe Name, Kind, Kind)
assertTypeConstructor = assertMatch mismatchKinds _KArrow "_ -> _"


-- Judgements

switch :: (Has (Reader ElabContext) sig m, Has (Throw ErrReason) sig m) => m (a :==> Kind) -> Kind <==: m a
switch m = Check $ \ _K -> do
  a :==> _KA <- m
  a <$ unless (_KA == _K) (couldNotUnifyKinds (Exp _K) (Act _KA))
