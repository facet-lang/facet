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
, checkType
  -- * Judgements
, checkIsType
, IsType(..)
, mapIsType
) where

import           Control.Algebra
import           Control.Effect.Lens (views)
import           Control.Effect.State
import           Control.Effect.Throw
import           Data.Bifunctor (first)
import           Data.Foldable (foldl')
import           Data.Functor (($>))
import           Facet.Context
import           Facet.Core.Type
import           Facet.Elab
import           Facet.Name
import           Facet.Semiring (Few(..), one, zero)
import qualified Facet.Surface as S
import           Facet.Syntax
import           GHC.Stack

tvar :: (HasCallStack, Has (Throw Err) sig m) => QName -> Synth m TExpr
tvar n = Synth $ views context_ (lookupInContext n) >>= \case
  Just (i, q, _T) -> use i q $> (TVar (Free (Right i)) ::: _T)
  Nothing         -> do
    q :=: _ ::: _T <- resolveQ n
    instantiate TInst $ TVar (Global q) ::: _T


_Type :: Synth m TExpr
_Type = Synth $ pure $ TType ::: VType

_Interface :: Synth m TExpr
_Interface = Synth $ pure $ TInterface ::: VType

_String :: Synth m TExpr
_String = Synth $ pure $ TString ::: VType


forAll :: (HasCallStack, Has (Throw Err) sig m) => Name ::: Check m TExpr -> Check m TExpr -> Synth m TExpr
forAll (n ::: t) b = Synth $ do
  t' <- check (t ::: VType)
  env <- views context_ toEnv
  subst <- get
  let vt = eval subst (Left <$> env) t'
  b' <- Binding n zero vt |- check (b ::: VType)
  pure $ TForAll n t' b' ::: VType

(-->) :: Algebra sig m => Maybe Name ::: Check m (Quantity, TExpr) -> Check m TExpr -> Synth m TExpr
(n ::: a) --> b = Synth $ do
  (q', a') <- check (a ::: VType)
  b' <- check (b ::: VType)
  pure $ TArrow n q' a' b' ::: VType

infixr 1 -->


comp :: Algebra sig m => [Check m TExpr] -> Check m TExpr -> Synth m TExpr
comp s t = Synth $ do
  s' <- traverse (check . (::: VInterface)) s
  -- FIXME: classify types by universe (value/computation) and check that this is a value type being returned
  t' <- check (t ::: VType)
  pure $ TComp s' t' ::: VType


synthType :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> Synth m TExpr
synthType (S.Ann s _ e) = mapSynth (pushSpan s) $ case e of
  S.TVar n          -> tvar n
  S.KType           -> _Type
  S.KInterface      -> _Interface
  S.TString         -> _String
  S.TForAll n t b   -> forAll (n ::: checkType t) (checkType b)
  S.TArrow  n q a b -> (n ::: ((maybe Many interpretMul q,) <$> checkType a)) --> checkType b
  S.TComp s t       -> comp (map checkInterface s) (checkType t)
  S.TApp f a        -> app TApp (synthType f) (checkType a)
  where
  interpretMul = \case
    S.Zero -> zero
    S.One  -> one

-- | Check a type at a kind.
--
-- NB: while synthesis is possible for all types at present, I reserve the right to change that.
checkType :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> Check m TExpr
checkType = switch . synthType

synthInterface :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Interface -> Synth m TExpr
synthInterface (S.Ann s _ (S.Interface (S.Ann sh _ h) sp)) = mapSynth (pushSpan s) $
  foldl' (app TApp) h' (checkType <$> sp)
  where
  h' = mapSynth (pushSpan sh) (tvar h)

checkInterface :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Interface -> Check m TExpr
checkInterface = switch . synthInterface


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
