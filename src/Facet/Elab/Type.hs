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
import           Control.Effect.Reader
import           Control.Effect.Throw
import           Control.Monad (unless)
import           Facet.Elab
import           Facet.Functor.Check
import           Facet.Functor.Synth
import           Facet.Graph (Graph)
import           Facet.Interface
import           Facet.Kind
import           Facet.Lens (views)
import           Facet.Module
import           Facet.Name
import           Facet.Snoc
import qualified Facet.Surface.Type.Expr as S
import           Facet.Syntax as S hiding (context_)
import qualified Facet.Type.Expr as TX

tvar :: (Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (Throw ErrReason) sig m) => QName -> m (TX.Type :==> Kind)
tvar n = views typeContext_ (lookupInTypeContext n) >>= \case
  [(n', _K)] -> pure (TX.Var (Bound (Right n')) :==> _K)
  _          -> resolveDef n >>= \case
    DSubmodule _ _K -> pure $ TX.Var (Free n) :==> _K
    _               -> freeVariable n

ivar :: (Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (Throw ErrReason) sig m) => QName -> m (QName :==> Kind)
ivar n = resolveDef n >>= \case
    DSubmodule (SInterface _) _K -> pure $ n :==> _K
    _                            -> freeVariable n


_String :: Applicative m => m (TX.Type :==> Kind)
_String = pure $ TX.String :==> KType


forAll :: (Has (Reader ElabContext) sig m, Has (Throw ErrReason) sig m) => Name ::: Kind -> m (TX.Type :==> Kind) -> m (TX.Type :==> Kind)
forAll (n ::: t) b = do
  b' <- n :==> t ||- switch b <==: KType
  pure $ TX.ForAll n t b' :==> KType

arrow :: (Has (Reader ElabContext) sig m, Has (Throw ErrReason) sig m) => (a -> b -> c) -> m (a :==> Kind) -> m (b :==> Kind) -> m (c :==> Kind)
arrow mk a b = do
  a' <- switch a <==: KType
  b' <- switch b <==: KType
  pure $ mk a' b' :==> KType


app :: (Has (Reader ElabContext) sig m, Has (Throw ErrReason) sig m) => (a -> b -> c) -> m (a :==> Kind) -> m (b :==> Kind) -> m (c :==> Kind)
app mk f a = do
  f' :==> _F <- f
  (_, _A, _B) <- assertTypeConstructor _F
  -- FIXME: assert that the usage is zero
  a' <- switch a <==: _A
  pure $ mk f' a' :==> _B


comp :: (Has (Reader ElabContext) sig m, Has (Throw ErrReason) sig m) => [m (Interface TX.Type :==> Kind)] -> m (TX.Type :==> Kind) -> m (TX.Type :==> Kind)
comp s t = do
  s' <- traverse ((<==: KInterface) . switch) s
  -- FIXME: polarize types and check that this is a value type being returned
  t' <- switch t <==: KType
  pure $ TX.Comp (fromInterfaces s') t' :==> KType


synthType :: (Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (Throw ErrReason) sig m) => S.Ann S.Type -> m (TX.Type :==> Kind)
synthType (S.Ann s _ e) = pushSpan s $ case e of
  S.TVar n        -> tvar n
  S.TString       -> Facet.Elab.Type._String
  S.TForAll n t b -> forAll (n ::: t) (synthType b)
  S.TArrow  n a b -> arrow (TX.Arrow n) (synthType a) (synthType b)
  S.TComp s t     -> comp (map synthInterface s) (synthType t)
  S.TApp f a      -> app TX.App (synthType f) (synthType a)

synthInterface :: (Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (Throw ErrReason) sig m) => S.Ann (S.Interface (S.Ann S.Type)) -> m (Interface TX.Type :==> Kind)
synthInterface (S.Ann s _ (S.Interface h sp)) = pushSpan s $ do
  -- FIXME: check that the application actually result in an Interface
  h' :==> _ <- ivar h
  sp' <- foldl' (liftA2 (:>)) (pure Nil) ((<==: KType) . switch . synthType <$> sp)
  pure $ Interface h' sp' :==> KInterface


-- Assertions

assertTypeConstructor :: Has (Throw ErrReason) sig m => Kind -> m (Maybe Name, Kind, Kind)
assertTypeConstructor = assertMatch mismatchKinds _KArrow "_ -> _"


-- Judgements

switch :: (Has (Reader ElabContext) sig m, Has (Throw ErrReason) sig m) => m (a :==> Kind) -> Kind <==: m a
switch m = Check $ \ _K -> do
  a :==> _KA <- m
  a <$ unless (_KA == _K) (couldNotUnifyKinds (Exp _K) (Act _KA))
