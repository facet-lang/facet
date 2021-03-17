{-# LANGUAGE OverloadedStrings #-}
module Facet.Elab.Type
( -- * Types
  tvar
, _Type
, _Interface
, _String
, forAll
, (-->)
, synthType
  -- * Judgements
, checkIsType
, IsType(..)
, mapIsType
) where

import           Control.Algebra
import           Control.Effect.Lens (views)
import           Control.Effect.State
import           Control.Effect.Throw
import           Control.Effect.Writer (censor)
import           Data.Bifunctor (first)
import           Data.Foldable (foldl')
import           Data.Functor (($>))
import           Facet.Context
import           Facet.Core.Type
import           Facet.Elab
import           Facet.Name
import           Facet.Semiring (Few(..), one, zero, (><<))
import qualified Facet.Surface as S
import           Facet.Syntax
import           Facet.Usage (Usage)
import           GHC.Stack

tvar :: (HasCallStack, Has (Throw Err) sig m) => QName -> IsType m TExpr
tvar n = IsType $ views context_ (lookupInContext n) >>= \case
  Just (i, q, Right _T) -> use i q $> (TVar (Free (Right i)) ::: _T)
  _                     -> do
    q :=: _ ::: _T <- resolveQ n
    pure $ TVar (Global q) ::: _T


_Type :: IsType m TExpr
_Type = IsType $ pure $ TType ::: VType

_Interface :: IsType m TExpr
_Interface = IsType $ pure $ TInterface ::: VType

_String :: IsType m TExpr
_String = IsType $ pure $ TString ::: VType


forAll :: (HasCallStack, Has (Throw Err) sig m) => Name ::: IsType m TExpr -> IsType m TExpr -> IsType m TExpr
forAll (n ::: t) b = IsType $ do
  t' <- checkIsType (t ::: VType)
  env <- views context_ toEnv
  subst <- get
  let vt = eval subst (Left <$> env) t'
  b' <- Binding n zero (Right vt) |- checkIsType (b ::: VType)
  pure $ TForAll n t' b' ::: VType

(-->) :: (HasCallStack, Has (Throw Err) sig m) => Maybe Name ::: IsType m (Quantity, TExpr) -> IsType m TExpr -> IsType m TExpr
(n ::: a) --> b = IsType $ do
  (q', a') <- checkIsType (a ::: VType)
  b' <- checkIsType (b ::: VType)
  pure $ TArrow n q' a' b' ::: VType

infixr 1 -->


app :: (HasCallStack, Has (Throw Err) sig m) => (a -> b -> c) -> IsType m a -> IsType m b -> IsType m c
app mk f a = IsType $ do
  f' ::: _F <- isType f
  (_ ::: (q, _A), _B) <- assertFunction _F
  -- FIXME: assert that the usage is zero
  a' <- censor @Usage (q ><<) $ checkIsType (a ::: _A)
  pure $ mk f' a' ::: _B


comp :: (HasCallStack, Has (Throw Err) sig m) => [IsType m TExpr] -> IsType m TExpr -> IsType m TExpr
comp s t = IsType $ do
  s' <- traverse (checkIsType . (::: VInterface)) s
  -- FIXME: polarize types and check that this is a value type being returned
  t' <- checkIsType (t ::: VType)
  pure $ TComp s' t' ::: VType


synthType :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> IsType m TExpr
synthType (S.Ann s _ e) = mapIsType (pushSpan s) $ case e of
  S.TVar n          -> tvar n
  S.KType           -> _Type
  S.KInterface      -> _Interface
  S.TString         -> _String
  S.TForAll n t b   -> forAll (n ::: synthType t) (synthType b)
  S.TArrow  n q a b -> (n ::: ((maybe Many interpretMul q,) <$> synthType a)) --> synthType b
  S.TComp s t       -> comp (map synthInterface s) (synthType t)
  S.TApp f a        -> app TApp (synthType f) (synthType a)
  where
  interpretMul = \case
    S.Zero -> zero
    S.One  -> one

synthInterface :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Interface -> IsType m TExpr
synthInterface (S.Ann s _ (S.Interface (S.Ann sh _ h) sp)) = mapIsType (pushSpan s) $
  foldl' (app TApp) h' (synthType <$> sp)
  where
  h' = mapIsType (pushSpan sh) (tvar h)


-- Judgements

checkIsType :: (HasCallStack, Has (Throw Err) sig m) => IsType m a ::: Type -> Elab m a
checkIsType (m ::: _K) = do
  a ::: _KA <- isType m
  a <$ unify _KA _K

newtype IsType m a = IsType { isType :: Elab m (a ::: Type) }

instance Functor (IsType m) where
  fmap f (IsType m) = IsType (first f <$> m)

mapIsType :: (Elab m (a ::: Type) -> Elab m (b ::: Type)) -> IsType m a -> IsType m b
mapIsType f = IsType . f . isType
