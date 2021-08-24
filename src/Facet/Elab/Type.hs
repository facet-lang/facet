{-# LANGUAGE OverloadedStrings #-}
module Facet.Elab.Type
( -- * Types
  tvar
, _Type
, _Interface
, _String
, forAll
, synthKind
, synthType
  -- * Judgements
, checkIsType
) where

import           Control.Algebra
import           Control.Applicative (liftA2)
import           Control.Effect.Throw
import           Control.Monad (unless)
import           Data.Foldable (foldl')
import           Data.Functor (($>))
import           Facet.Elab
import           Facet.Functor.Synth
import           Facet.Interface
import           Facet.Kind
import           Facet.Lens (views)
import           Facet.Module
import           Facet.Name
import           Facet.Pattern
import           Facet.Semiring (Few(..), one, zero)
import           Facet.Snoc
import qualified Facet.Surface as S
import           Facet.Syntax
import qualified Facet.Type.Expr as TX
import           Facet.Type.Norm
import           GHC.Stack

tvar :: (HasCallStack, Has (Throw Err) sig m) => QName -> Elab m (TX.Type :==> Kind)
tvar n = views context_ (lookupInContext n) >>= \case
  [(n', q, CK _K)] -> use n' q $> (TX.Var (Free (Right n')) :==> _K)
  _                -> resolveQ n >>= \case
    q :=: DData      _ _K -> pure $ TX.Var (Global q) :==> _K
    q :=: DInterface _ _K -> pure $ TX.Var (Global q) :==> _K
    _                     -> freeVariable n

ivar :: (HasCallStack, Has (Throw Err) sig m) => QName -> Elab m (RName :==> Kind)
ivar n = resolveQ n >>= \case
    q :=: DInterface _ _K -> pure $ q :==> _K
    _                     -> freeVariable n


_Type :: Elab m (Kind :==> Kind)
_Type = pure $ KType :==> KType

_Interface :: Elab m (Kind :==> Kind)
_Interface = pure $ KInterface :==> KType

_String :: Elab m (TX.Type :==> Kind)
_String = pure $ TX.String :==> KType


forAll :: (HasCallStack, Has (Throw Err) sig m) => Name ::: Elab m (Kind :==> Kind) -> Elab m (TX.Type :==> Kind) -> Elab m (TX.Type :==> Kind)
forAll (n ::: t) b = do
  t' <- checkIsType (t ::: KType)
  b' <- (zero, PVar (n ::: CK t')) |- checkIsType (b ::: KType)
  pure $ TX.ForAll n t' b' :==> KType

arrow :: (HasCallStack, Has (Throw Err) sig m) => (a -> b -> c) -> Elab m (a :==> Kind) -> Elab m (b :==> Kind) -> Elab m (c :==> Kind)
arrow mk a b = do
  a' <- checkIsType (a ::: KType)
  b' <- checkIsType (b ::: KType)
  pure $ mk a' b' :==> KType


app :: (HasCallStack, Has (Throw Err) sig m) => (a -> b -> c) -> Elab m (a :==> Kind) -> Elab m (b :==> Kind) -> Elab m (c :==> Kind)
app mk f a = do
  f' :==> _F <- f
  (_ ::: _A, _B) <- assertTypeConstructor _F
  -- FIXME: assert that the usage is zero
  a' <- checkIsType (a ::: _A)
  pure $ mk f' a' :==> _B


comp :: (HasCallStack, Has (Throw Err) sig m) => [Elab m (Interface TX.Type :==> Kind)] -> Elab m (TX.Type :==> Kind) -> Elab m (TX.Type :==> Kind)
comp s t = do
  s' <- traverse (checkIsType . (::: KInterface)) s
  -- FIXME: polarize types and check that this is a value type being returned
  t' <- checkIsType (t ::: KType)
  pure $ TX.Comp (fromInterfaces s') t' :==> KType


synthKind :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Kind -> Elab m (Kind :==> Kind)
synthKind (S.Ann s _ e) = pushSpan s $ case e of
  S.KArrow n a b -> arrow (KArrow n) (synthKind a) (synthKind b)
  S.KType        -> _Type
  S.KInterface   -> _Interface


synthType :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> Elab m (TX.Type :==> Kind)
synthType (S.Ann s _ e) = pushSpan s $ case e of
  S.TVar n          -> tvar n
  S.TString         -> _String
  S.TForAll n t b   -> forAll (n ::: synthKind t) (synthType b)
  S.TArrow  n q a b -> arrow (TX.Arrow n (maybe Many interpretMul q)) (synthType a) (synthType b)
  S.TComp s t       -> comp (map synthInterface s) (synthType t)
  S.TApp f a        -> app TX.App (synthType f) (synthType a)
  where
  interpretMul = \case
    S.Zero -> zero
    S.One  -> one

synthInterface :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Interface -> Elab m (Interface TX.Type :==> Kind)
synthInterface (S.Ann s _ (S.Interface (S.Ann sh _ h) sp)) = pushSpan s $ do
  -- FIXME: check that the application actually result in an Interface
  h' :==> _ <- pushSpan sh (ivar h)
  sp' <- foldl' (liftA2 (:>)) (pure Nil) (checkIsType . (::: KType) . synthType <$> sp)
  pure $ Interface h' sp' :==> KInterface


-- Assertions

assertTypeConstructor :: (HasCallStack, Has (Throw Err) sig m) => Kind -> Elab m (Maybe Name ::: Kind, Kind)
assertTypeConstructor = assertMatch (\case{ KArrow n t b -> pure (n ::: t, b) ; _ -> Nothing }) "_ -> _"


-- Judgements

checkIsType :: (HasCallStack, Has (Throw Err) sig m) => Elab m (a :==> Kind) ::: Kind -> Elab m a
checkIsType (m ::: _K) = do
  a :==> _KA <- m
  a <$ unless (_KA == _K) (couldNotUnify (Exp (CK _K)) (Act (CK _KA)))
