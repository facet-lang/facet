{-# LANGUAGE OverloadedStrings #-}
module Facet.Elab.Type
( -- * Types
  _Type
, _Interface
, _String
, forAll
, elabKind
, elabNType
, elabPType
  -- * Judgements
, checkIsType
, IsType(..)
, mapIsType
) where

import           Control.Algebra
import           Control.Effect.Lens (views)
import           Control.Effect.Throw
import           Control.Monad (unless)
import           Data.Bifunctor (first)
import           Data.Foldable (foldl')
import           Data.Functor (($>))
import           Facet.Context
import           Facet.Core.Module
import           Facet.Core.Type hiding (global)
import           Facet.Elab
import           Facet.Name
import           Facet.Semiring (Few(..), one, zero)
import qualified Facet.Surface as S
import           Facet.Syntax
import           GHC.Stack

var :: (HasCallStack, Has (Throw Err) sig m) => (Var Meta Index -> a) -> QName -> IsType m a
var mk n = IsType $ views context_ (lookupInContext n) >>= \case
  Just (i, q, SType _T) -> use i q $> (mk (Free i) ::: _T)
  _                     -> isType (mk . Global <$> global n)

global :: (HasCallStack, Has (Throw Err) sig m) => QName -> IsType m QName
global n = IsType $ do
  q :=: d <- resolveQ n
  _T <- case d of
    DData      _ _K -> pure _K
    DInterface _ _K -> pure _K
    _               -> freeVariable q
  pure $ q ::: _T


_Type :: IsType m Kind
_Type = IsType $ pure $ Type ::: Type

_Interface :: IsType m Kind
_Interface = IsType $ pure $ Interface ::: Type

_String :: IsType m PTExpr
_String = IsType $ pure $ TString ::: Type


forAll :: (HasCallStack, Has (Throw Err) sig m) => Name ::: IsType m Kind -> IsType m PTExpr -> IsType m PTExpr
forAll (n ::: t) b = IsType $ do
  t' <- checkIsType (t ::: Type)
  b' <- Binding n zero (SType t') |- checkIsType (b ::: Type)
  pure $ TForAll n t' b' ::: Type

arrow :: (HasCallStack, Has (Throw Err) sig m) => (a -> b -> c) -> IsType m a -> IsType m b -> IsType m c
arrow mk a b = IsType $ do
  a' <- checkIsType (a ::: Type)
  b' <- checkIsType (b ::: Type)
  pure $ mk a' b' ::: Type

function :: (HasCallStack, Has (Throw Err) sig m) => Maybe Name ::: (Quantity, IsType m PTExpr) -> IsType m NTExpr -> IsType m NTExpr
function (n ::: (q, a)) = arrow (TArrow n q) a


comp :: (HasCallStack, Has (Throw Err) sig m) => [IsType m Interface] -> IsType m PTExpr -> IsType m NTExpr
comp s t = IsType $ do
  s' <- traverse (checkIsType . (::: Interface)) s
  t' <- checkIsType (t ::: Type)
  pure $ TComp s' t' ::: Type

app :: (HasCallStack, Has (Throw Err) sig m) => (a -> b -> c) -> IsType m a -> IsType m b -> IsType m c
app mk f a = IsType $ do
  f' ::: _F <- isType f
  -- FIXME: assert that the usage is zero.
  (_ ::: _A, _B) <- assertTypeConstructor "in application" _F
  a' <- checkIsType (a ::: _A)
  pure $ mk f' a' ::: _B

thunk :: (HasCallStack, Has (Throw Err) sig m) => IsType m NTExpr -> IsType m PTExpr
thunk t = IsType $ do
  t' <- checkIsType (t ::: Type)
  pure $ TThunk t' ::: Type


elabKind :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> IsType m Kind
elabKind (S.Ann s _ e) = mapIsType (pushSpan s) $ case e of
  S.TArrow n _ a b -> arrow (KArrow n) (elabKind a) (elabKind b)
  S.TApp f a       -> app kapp (elabKind f) (elabKind a)
  S.TVar n         -> kglobal <$> global n
  S.KType          -> _Type
  S.KInterface     -> _Interface
  S.TComp{}        -> nope
  S.TForAll{}      -> nope
  S.TString        -> nope
  where
  nope = IsType $ couldNotSynthesize (show e <> " at the kind level")


elabNType :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> IsType m NTExpr
elabNType expr@(S.Ann s _ e) = mapIsType (pushSpan s) $ case e of
  S.TForAll{}       -> comp [] (elabPType expr)
  S.TArrow  n q a b -> function (n ::: (maybe Many interpretMul q, elabPType a)) (comp [] (elabPType b))
  S.TComp s t       -> comp (map synthInterface s) (elabPType t)
  S.TApp{}          -> comp [] (elabPType expr)
  S.TVar{}          -> comp [] (elabPType expr)
  S.TString         -> comp [] (elabPType expr)
  S.KType           -> nope
  S.KInterface      -> nope
  where
  nope = IsType $ couldNotSynthesize (show e <> " at the type level")

elabPType :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> IsType m PTExpr
elabPType expr@(S.Ann s _ e) = mapIsType (pushSpan s) $ case e of
  S.TForAll n t b -> forAll (n ::: elabKind t) (elabPType b)
  S.TArrow{}      -> thunk (elabNType expr)
  S.TComp{}       -> thunk (elabNType expr)
  S.TApp f a      -> app TApp (elabPType f) (elabPType a)
  S.TVar n        -> var TVar n
  S.TString       -> _String
  S.KType         -> nope
  S.KInterface    -> nope
  where
  nope = IsType $ couldNotSynthesize (show e <> " at the type level")


interpretMul :: S.Mul -> Few
interpretMul = \case
  S.Zero -> zero
  S.One  -> one


synthInterface :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Interface -> IsType m Interface
synthInterface (S.Ann s _ (S.Interface (S.Ann sh _ h) sp)) = mapIsType (pushSpan s) . fmap IInterface $
  foldl' (app kapp) (mapIsType (pushSpan sh) (kglobal <$> global h)) (elabKind <$> sp)


assertTypeConstructor :: (HasCallStack, Has (Throw Err) sig m) => String -> Kind -> Elab m (Maybe Name ::: Kind, Kind)
assertTypeConstructor = assertKind (\case{ KArrow n t b -> pure (n ::: t, b) ; _ -> Nothing }) "_ -> _"


-- Judgements

checkIsType :: (HasCallStack, Has (Throw Err) sig m) => IsType m a ::: Kind -> Elab m a
checkIsType (m ::: _K) = do
  a ::: _KA <- isType m
  a <$ unless (_KA == _K) (couldNotUnify "kind mismatch" (EK _KA) (EK _K))

newtype IsType m a = IsType { isType :: Elab m (a ::: Kind) }

instance Functor (IsType m) where
  fmap f (IsType m) = IsType (first f <$> m)

mapIsType :: (Elab m (a ::: Kind) -> Elab m (b ::: Kind)) -> IsType m a -> IsType m b
mapIsType f = IsType . f . isType
