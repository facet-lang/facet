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
) where

import           Control.Algebra
import           Control.Effect.Lens (views)
import           Control.Effect.State
import           Control.Effect.Throw
import           Control.Effect.Writer (censor)
import           Data.Foldable (foldl')
import           Data.Functor (($>))
import           Facet.Context
import           Facet.Core.Module
import           Facet.Core.Type
import           Facet.Elab
import           Facet.Name
import           Facet.Semiring (Few(..), one, zero, (><<))
import qualified Facet.Surface as S
import           Facet.Syntax
import           Facet.Usage
import           GHC.Stack

tvar :: (HasCallStack, Has (Throw Err) sig m) => QName -> Synth m TExpr
tvar n = Synth $ views context_ (lookupInContext n) >>= \case
  Just (i, q, _T) -> use i q $> (TVar (Free i) ::: _T)
  _                  -> do
    q :=: d <- resolveQ n
    _T <- case d of
      DData      _ _K -> pure _K
      DInterface _ _K -> pure _K
      _               -> freeVariable q
    pure $ TVar (Global q) ::: _T


_Type :: Synth m TExpr
_Type = Synth $ pure $ TType ::: Type

_Interface :: Synth m TExpr
_Interface = Synth $ pure $ TInterface ::: Type

_String :: Synth m TExpr
_String = Synth $ pure $ TString ::: Type


forAll :: (HasCallStack, Has (Throw Err) sig m) => Name ::: Check m TExpr -> Check m TExpr -> Synth m TExpr
forAll (n ::: t) b = Synth $ do
  t' <- check (t ::: Type)
  env <- views context_ toEnv
  subst <- get
  let vt = eval subst (Left <$> env) t'
  b' <- Binding n zero vt |- check (b ::: Type)
  pure $ TForAll n t' b' ::: Type

(-->) :: Algebra sig m => Maybe Name ::: Check m (Quantity, TExpr) -> Check m TExpr -> Synth m TExpr
(n ::: a) --> b = Synth $ do
  (q', a') <- check (a ::: Type)
  b' <- check (b ::: Type)
  pure $ TArrow n q' a' b' ::: Type

infixr 1 -->


comp :: Algebra sig m => [Check m (Interface TExpr)] -> Check m TExpr -> Synth m TExpr
comp s t = Synth $ do
  s' <- traverse (check . (::: Interface)) s
  t' <- check (t ::: Type)
  pure $ TComp s' t' ::: Type


tapp :: (HasCallStack, Has (Throw Err) sig m) => Synth m TExpr -> Check m TExpr -> Synth m TExpr
tapp f a = Synth $ do
  f' ::: _F <- synth f
  -- FIXME: verify that the quantity is zero?
  (_ ::: (_, _A), _B) <- expectFunction "in type-level application" _F
  a' <- censor @Usage (zero ><<) $ check (a ::: _A)
  pure $ TApp f' a' ::: _B


synthType :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> Synth m TExpr
synthType (S.Ann s _ e) = mapSynth (pushSpan s) $ case e of
  S.TForAll n t b   -> forAll (n ::: switch (synthType t)) (switch (synthType b))
  S.TArrow  n q a b -> (n ::: ((maybe Many interpretMul q,) <$> switch (pos (synthType a)))) --> switch (neg (synthType b))
  S.TComp s t       -> comp (map (switch . synthInterface) s) (switch (pos (synthType t)))
  S.TApp f a        -> tapp (synthType f) (switch (synthType a))
  S.TVar n          -> tvar n
  S.KType           -> _Type
  S.KInterface      -> _Interface
  S.TString         -> _String
  where
  pos b = Synth $ do
    t ::: _T <- synth b
    pure $ (if not (isNeg t) then t else TThunk t) ::: _T
  isPos = \case
    TVar{}   -> True
    TString  -> True
    TThunk{} -> True
    _        -> False
  neg b = Synth $ do
    t ::: _T <- synth b
    pure $ (if not (isPos t) then t else TComp [] t) ::: _T
  isNeg = \case
    TForAll{} -> True
    TArrow{}  -> True
    TComp{}   -> True
    _         -> False
  interpretMul = \case
    S.Zero -> zero
    S.One  -> one


synthInterface :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Interface -> Synth m (Interface TExpr)
synthInterface (S.Ann s _ (S.Interface (S.Ann sh _ h) sp)) = mapSynth (pushSpan s) . fmap IInterface $
  foldl' tapp (mapSynth (pushSpan sh) (tvar h)) (switch . synthType <$> sp)
