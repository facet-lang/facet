{-# LANGUAGE OverloadedStrings #-}
module Facet.Elab.Type
( -- * Types
  tvar
, _Type
, _Interface
, _String
, forAll
, (-->)
, synthTypeC
, synthTypeV
, checkTypeC
, checkTypeV
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

tvar :: (HasCallStack, Has (Throw Err) sig m) => Q Name -> Synth m (TExpr V)
tvar n = Synth $ views context_ (lookupInContext n) >>= \case
  Just (i, q, _T) -> use i q $> (TVar (Free i) ::: _T)
  Nothing         -> do
    q :=: _ ::: _T <- resolveQ n
    pure $ TVar (Global q) ::: _T


_Type :: Synth m (TExpr V)
_Type = Synth $ pure $ TType ::: Type

_Interface :: Synth m (TExpr V)
_Interface = Synth $ pure $ TInterface ::: Type

_String :: Synth m (TExpr V)
_String = Synth $ pure $ TString ::: Type


forAll :: (HasCallStack, Has (Throw Err) sig m) => Name ::: Check m (TExpr V) -> Check m (TExpr C) -> Synth m (TExpr C)
forAll (n ::: t) b = Synth $ do
  t' <- check (t ::: Type)
  env <- views context_ toEnv
  subst <- get
  let vt = eval subst (Left <$> env) t'
  b' <- Binding n zero vt |- check (b ::: Type)
  pure $ TForAll n t' b' ::: Type

(-->) :: Algebra sig m => Maybe Name ::: Check m (Quantity, TExpr V) -> Check m (TExpr C) -> Synth m (TExpr C)
(n ::: a) --> b = Synth $ do
  (q', a') <- check (a ::: Type)
  b' <- check (b ::: Type)
  pure $ TArrow n q' a' b' ::: Type

infixr 1 -->


comp :: Algebra sig m => [Check m (TExpr V)] -> Check m (TExpr V) -> Synth m (TExpr C)
comp s t = Synth $ do
  s' <- traverse (check . (::: Interface)) s
  -- FIXME: classify types by universe (value/computation) and check that this is a value type being returned
  t' <- check (t ::: Type)
  pure $ TComp s' t' ::: Type


synthTypeC :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> Synth m (TExpr C)
synthTypeC ty@(S.Ann s _ e) = mapSynth (pushSpan s) $ case e of
  S.TForAll n t b   -> forAll (n ::: checkTypeV t) (checkTypeC b)
  S.TArrow  n q a b -> (n ::: ((maybe Many interpretMul q,) <$> checkTypeV a)) --> checkTypeC b
  S.TComp s t       -> comp (map checkInterfaceV s) (checkTypeV t)
  S.TApp f a        -> app TApp (synthTypeC f) (checkTypeV a)
  S.TVar{}          -> shift
  S.KType           -> shift
  S.KInterface      -> shift
  S.TString         -> shift
  where
  shift = Synth $ do
    _T ::: _K <- synth (synthTypeV ty)
    pure $ TComp [] _T ::: _K
  interpretMul = \case
    S.Zero -> zero
    S.One  -> one

synthTypeV :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> Synth m (TExpr V)
synthTypeV ty@(S.Ann s _ e) = mapSynth (pushSpan s) $ case e of
  S.TVar n     -> tvar n -- FIXME: instantiate in synthType instead
  S.KType      -> _Type
  S.KInterface -> _Interface
  S.TString    -> _String
  S.TForAll{}  -> shift
  S.TArrow{}   -> shift
  S.TComp{}    -> shift
  S.TApp{}     -> shift
  where
  shift = TThunk <$> synthTypeC ty

-- | Check a type at a kind.
--
-- NB: while synthesis is possible for all types at present, I reserve the right to change that.
checkTypeC :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> Check m (TExpr C)
checkTypeC = switch . synthTypeC

-- | Check a type at a kind.
--
-- NB: while synthesis is possible for all types at present, I reserve the right to change that.
checkTypeV :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> Check m (TExpr V)
checkTypeV = switch . synthTypeV

synthInterfaceC :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Interface -> Synth m (TExpr C)
synthInterfaceC (S.Ann s _ (S.Interface (S.Ann sh _ h) sp)) = mapSynth (pushSpan s) $
  foldl' (app TApp) h' (checkTypeV <$> sp)
  where
  h' = mapSynth (pushSpan sh . fmap (first (TComp []))) (tvar h)

checkInterfaceV :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Interface -> Check m (TExpr V)
checkInterfaceV = switch . fmap TThunk . synthInterfaceC
