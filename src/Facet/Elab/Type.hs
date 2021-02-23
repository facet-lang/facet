{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
module Facet.Elab.Type
( -- * Types
  tvar
, _Type
, _Interface
, _String
, forAll
, (-->)
, synthTypeN
, synthTypeP
, checkTypeN
, checkTypeP
) where

import           Control.Algebra
import           Control.Effect.Lens (views)
import           Control.Effect.State
import           Control.Effect.Throw
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

tvar :: (HasCallStack, Has (Throw Err) sig m) => Q Name -> Synth T m (TExpr T)
tvar n = Synth $ views context_ (lookupInContext n) >>= \case
  Just (i, q, _T) -> use i q $> (TVar (Free i) ::: _T)
  Nothing         -> do
    q :=: _ ::: _T <- resolveQ n
    pure $ TVar (Global q) ::: _T


_Type :: Synth T m (TExpr T)
_Type = Synth $ pure $ TType ::: Type

_Interface :: Synth T m (TExpr T)
_Interface = Synth $ pure $ TInterface ::: Type

_String :: Synth T m (TExpr P)
_String = Synth $ pure $ TString ::: Type


forAll :: (HasCallStack, Has (Throw Err) sig m) => Name ::: Check T m (TExpr T) -> Check T m (TExpr N) -> Synth T m (TExpr N)
forAll (n ::: t) b = Synth $ do
  t' <- check (t ::: Type)
  env <- views context_ toEnv
  subst <- get
  let vt = eval subst (Left <$> env) t'
  b' <- Binding n zero vt |- check (b ::: Type)
  pure $ TForAll n t' b' ::: Type

(-->) :: Algebra sig m => Maybe Name ::: Check T m (Quantity, TExpr P) -> Check T m (TExpr N) -> Synth T m (TExpr N)
(n ::: a) --> b = Synth $ do
  (q', a') <- check (a ::: Type)
  b' <- check (b ::: Type)
  pure $ TArrow n q' a' b' ::: Type

infixr 1 -->


comp :: Algebra sig m => [Check T m (TExpr P)] -> Check T m (TExpr P) -> Synth T m (TExpr N)
comp s t = Synth $ do
  s' <- traverse (check . (::: Interface)) s
  t' <- check (t ::: Type)
  pure $ TComp s' t' ::: Type


synthTypeN :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> Synth T m (TExpr N)
synthTypeN ty@(S.Ann s _ e) = mapSynth (pushSpan s) $ case e of
  S.TForAll n t b   -> forAll (n ::: checkTypeP t) (checkTypeN b)
  S.TArrow  n q a b -> (n ::: ((maybe Many interpretMul q,) <$> checkTypeP a)) --> checkTypeN b
  S.TComp s t       -> comp (map checkInterfaceV s) (checkTypeP t)
  S.TApp{}          -> toC
  S.TVar{}          -> toC
  S.KType           -> toC
  S.KInterface      -> toC
  S.TString         -> toC
  where
  toC = shiftP <$> synthTypeP ty
  interpretMul = \case
    S.Zero -> zero
    S.One  -> one

synthTypeP :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> Synth T m (TExpr P)
synthTypeP ty@(S.Ann s _ e) = mapSynth (pushSpan s) $ case e of
  S.TVar n     -> tvar n -- FIXME: instantiate in synthType instead
  S.KType      -> _Type
  S.KInterface -> _Interface
  S.TString    -> _String
  S.TApp f a   -> app TApp (synthTypeP f) (checkTypeP a)
  S.TForAll{}  -> toV
  S.TArrow{}   -> toV
  S.TComp{}    -> toV
  where
  toV = shiftN <$> synthTypeN ty

-- | Check a type at a kind.
--
-- NB: while synthesis is possible for all types at present, I reserve the right to change that.
checkTypeN :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> Check T m (TExpr N)
checkTypeN = switch . synthTypeN

-- | Check a type at a kind.
--
-- NB: while synthesis is possible for all types at present, I reserve the right to change that.
checkTypeP :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> Check T m (TExpr P)
checkTypeP = switch . synthTypeP

synthInterfaceC :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Interface -> Synth T m (TExpr P)
synthInterfaceC (S.Ann s _ (S.Interface (S.Ann sh _ h) sp)) = mapSynth (pushSpan s) $
  foldl' (app TApp) (mapSynth (pushSpan sh) (tvar h)) (checkTypeP <$> sp)

checkInterfaceV :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Interface -> Check T m (TExpr P)
checkInterfaceV = switch . synthInterfaceC
