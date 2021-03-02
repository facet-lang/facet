{-# LANGUAGE OverloadedStrings #-}
module Facet.Elab.Type
( -- * Types
  tvar
, _Type
, _Interface
, _String
, forAll
, (-->)
, elabKind
, elabType
, elabPosType
, elabNegType
) where

import           Control.Algebra
import           Control.Effect.Lens (views)
import           Control.Effect.State
import           Control.Effect.Throw
import           Data.Foldable (foldl')
import           Data.Functor (($>))
import           Facet.Context
import           Facet.Core.Module
import           Facet.Core.Type
import           Facet.Elab
import           Facet.Name
import           Facet.Semiring (Few(..), one, zero)
import qualified Facet.Surface as S
import           Facet.Syntax
import           GHC.Stack

tvar :: (HasCallStack, Has (Throw Err) sig m) => QName -> Synth m (Pos TExpr)
tvar = var varT

kvar :: (HasCallStack, Has (Throw Err) sig m) => QName -> Synth m TExpr
kvar = var TVar

var :: (HasCallStack, Has (Throw Err) sig m) => (Var Meta Index -> a) -> QName -> Synth m a
var mk n = Synth $ views context_ (lookupInContext n) >>= \case
  Just (i, q, _T) -> use i q $> (mk (Free i) ::: _T)
  _               -> do
    q :=: d <- resolveQ n
    _T <- case d of
      DData      _ _K -> pure _K
      DInterface _ _K -> pure _K
      _               -> freeVariable q
    pure $ mk (Global q) ::: _T


_Type :: Synth m TExpr
_Type = Synth $ pure $ TType ::: Type

_Interface :: Synth m TExpr
_Interface = Synth $ pure $ TInterface ::: Type

_String :: Synth m (Pos TExpr)
_String = Synth $ pure $ stringT ::: Type


forAll :: (HasCallStack, Has (Throw Err) sig m) => Name ::: Check m TExpr -> Check m (Neg TExpr) -> Synth m (Neg TExpr)
forAll (n ::: t) b = Synth $ do
  t' <- check (t ::: Type)
  env <- views context_ toEnv
  subst <- get
  let vt = eval subst (Left <$> env) t'
  b' <- Binding n zero vt |- check (b ::: Type)
  pure $ forAllT n t' b' ::: Type

arrow :: Algebra sig m => (a -> b -> c) -> Check m a -> Check m b -> Synth m c
arrow mk a b = Synth $ do
  a' <- check (a ::: Type)
  b' <- check (b ::: Type)
  pure $ mk a' b' ::: Type

(-->) :: Algebra sig m => Maybe Name ::: (Quantity, Check m (Pos TExpr)) -> Check m (Neg TExpr) -> Synth m (Neg TExpr)
(n ::: (q, a)) --> b = arrow (arrowT n q) a b

infixr 1 -->


comp :: Algebra sig m => [Check m (Interface TExpr)] -> Check m (Pos TExpr) -> Synth m (Neg TExpr)
comp s t = Synth $ do
  s' <- traverse (check . (::: Interface)) s
  t' <- check (t ::: Type)
  pure $ compT s' t' ::: Type


elabKind :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> Synth m TExpr
elabKind (S.Ann s _ e) = mapSynth (pushSpan s) $ case e of
  S.TArrow  n q a b -> arrow (TArrow n (maybe Many interpretMul q)) (switch (elabKind a)) (switch (elabKind b))
  S.TApp f a        -> app TApp (elabKind f) (switch (elabKind a))
  S.TVar n          -> kvar n
  S.KType           -> _Type
  S.KInterface      -> _Interface
  S.TComp{}         -> nope
  S.TForAll{}       -> nope
  S.TString         -> nope
  where
  nope = Synth $ couldNotSynthesize (show e <> " at the kind level")

elabType :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> Synth m (Either (Neg TExpr) (Pos TExpr))
elabType (S.Ann s _ e) = mapSynth (pushSpan s) $ case e of
  S.TForAll n t b   -> Left <$> forAll (n ::: switch (elabKind t)) (switch (elabNegType b))
  S.TArrow  n q a b -> Left <$> ((n ::: (maybe Many interpretMul q, switch (elabPosType a))) --> switch (elabNegType b))
  S.TComp s t       -> Left <$> comp (map (switch . synthInterface) s) (switch (elabPosType t))
  S.TApp f a        -> Right <$> app appT (elabPosType f) (switch (elabPosType a))
  S.TVar n          -> Right <$> tvar n
  S.TString         -> Right <$> _String
  S.KType           -> nope
  S.KInterface      -> nope
  where
  nope = Synth $ couldNotSynthesize (show e <> " at the type level")

elabPosType :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> Synth m (Pos TExpr)
elabPosType = fmap (either thunkT id) . elabType

elabNegType :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> Synth m (Neg TExpr)
elabNegType = fmap (either id (compT [])) . elabType


interpretMul :: S.Mul -> Few
interpretMul = \case
  S.Zero -> zero
  S.One  -> one


synthInterface :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Interface -> Synth m (Interface TExpr)
synthInterface (S.Ann s _ (S.Interface (S.Ann sh _ h) sp)) = mapSynth (pushSpan s) . fmap IInterface $
  foldl' (app TApp) (mapSynth (pushSpan sh) (kvar h)) (switch . elabKind <$> sp)
