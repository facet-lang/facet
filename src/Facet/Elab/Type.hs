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
, IsType(..)
, mapIsType
) where

import           Control.Algebra
import           Control.Applicative (liftA2)
import           Control.Effect.Lens (views)
import           Control.Effect.Throw
import           Control.Monad (unless)
import           Data.Bifunctor (first)
import           Data.Foldable (foldl')
import           Data.Functor (($>))
import           Facet.Context
import           Facet.Core.Module
import           Facet.Core.Type
import           Facet.Elab
import           Facet.Name
import           Facet.Semiring (Few(..), one, zero)
import           Facet.Snoc
import qualified Facet.Surface as S
import           Facet.Syntax
import           GHC.Stack

tvar :: (HasCallStack, Has (Throw Err) sig m) => QName -> IsType m TExpr
tvar n = IsType $ views context_ (lookupInContext n) >>= \case
  [(i, q, Left _K)] -> use i q $> (TVar (Free (Right i)) ::: _K)
  _                 -> resolveQ n >>= \case
    q :=: DData      _ _K -> pure $ TVar (Global q) ::: _K
    q :=: DInterface _ _K -> pure $ TVar (Global q) ::: _K
    _                     -> freeVariable n

ivar :: (HasCallStack, Has (Throw Err) sig m) => QName -> IsType m RName
ivar n = IsType $ resolveQ n >>= \case
    q :=: DInterface _ _K -> pure $ q ::: _K
    _                     -> freeVariable n


_Type :: IsType m Kind
_Type = IsType $ pure $ KType ::: KType

_Interface :: IsType m Kind
_Interface = IsType $ pure $ KInterface ::: KType

_String :: IsType m TExpr
_String = IsType $ pure $ TString ::: KType


forAll :: (HasCallStack, Has (Throw Err) sig m) => Name ::: IsType m Kind -> IsType m TExpr -> IsType m TExpr
forAll (n ::: t) b = IsType $ do
  t' <- checkIsType (t ::: KType)
  b' <- Binding n zero (Left t') |- checkIsType (b ::: KType)
  pure $ TForAll n t' b' ::: KType

arrow :: (HasCallStack, Has (Throw Err) sig m) => (a -> b -> c) -> IsType m a -> IsType m b -> IsType m c
arrow mk a b = IsType $ do
  a' <- checkIsType (a ::: KType)
  b' <- checkIsType (b ::: KType)
  pure $ mk a' b' ::: KType


app :: (HasCallStack, Has (Throw Err) sig m) => (a -> b -> c) -> IsType m a -> IsType m b -> IsType m c
app mk f a = IsType $ do
  f' ::: _F <- isType f
  (_ ::: _A, _B) <- assertTypeConstructor _F
  -- FIXME: assert that the usage is zero
  a' <- checkIsType (a ::: _A)
  pure $ mk f' a' ::: _B


comp :: (HasCallStack, Has (Throw Err) sig m) => [IsType m (Interface TExpr)] -> IsType m TExpr -> IsType m TExpr
comp s t = IsType $ do
  s' <- traverse (checkIsType . (::: KInterface)) s
  -- FIXME: polarize types and check that this is a value type being returned
  t' <- checkIsType (t ::: KType)
  pure $ TComp s' t' ::: KType


synthKind :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Kind -> IsType m Kind
synthKind (S.Ann s _ e) = mapIsType (pushSpan s) $ case e of
  S.KArrow n a b -> arrow (KArrow n) (synthKind a) (synthKind b)
  S.KType        -> _Type
  S.KInterface   -> _Interface


synthType :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> IsType m TExpr
synthType (S.Ann s _ e) = mapIsType (pushSpan s) $ case e of
  S.TVar n          -> tvar n
  S.TString         -> _String
  S.TForAll n t b   -> forAll (n ::: synthKind t) (synthType b)
  S.TArrow  n q a b -> arrow (TArrow n (maybe Many interpretMul q)) (synthType a) (synthType b)
  S.TComp s t       -> comp (map synthInterface s) (synthType t)
  S.TApp f a        -> app TApp (synthType f) (synthType a)
  where
  interpretMul = \case
    S.Zero -> zero
    S.One  -> one

synthInterface :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Interface -> IsType m (Interface TExpr)
synthInterface (S.Ann s _ (S.Interface (S.Ann sh _ h) sp)) = IsType $ pushSpan s $ do
  -- FIXME: check that the application actually result in an Interface
  h' ::: _ <- pushSpan sh (isType (ivar h))
  sp' <- foldl' (liftA2 (:>)) (pure Nil) (checkIsType . (::: KType) . synthType <$> sp)
  pure $ Interface h' sp' ::: KInterface


-- Assertions

assertTypeConstructor :: (HasCallStack, Has (Throw Err) sig m) => Kind -> Elab m (Maybe Name ::: Kind, Kind)
assertTypeConstructor = assertMatch (\case{ SK (KArrow n t b) -> pure (n ::: t, b) ; _ -> Nothing }) "_ -> _" . SK


-- Judgements

checkIsType :: (HasCallStack, Has (Throw Err) sig m) => IsType m a ::: Kind -> Elab m a
checkIsType (m ::: _K) = do
  a ::: _KA <- isType m
  a <$ unless (_KA == _K) (couldNotUnify (Exp (SK _K)) (Act (SK _KA)))

newtype IsType m a = IsType { isType :: Elab m (a ::: Kind) }

instance Functor (IsType m) where
  fmap f (IsType m) = IsType (first f <$> m)

mapIsType :: (Elab m (a ::: Kind) -> Elab m (b ::: Kind)) -> IsType m a -> IsType m b
mapIsType f = IsType . f . isType
