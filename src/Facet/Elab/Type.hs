{-# LANGUAGE OverloadedStrings #-}
module Facet.Elab.Type
( -- * Types
  tvar
, _Type
, _Interface
, _String
, forAll
, (-->)
, comp
, synthType
, checkType
) where

import           Control.Algebra
import           Control.Effect.Lens (views)
import           Control.Effect.State
import           Control.Effect.Throw
import           Data.Foldable (foldl')
import           Facet.Context
import           Facet.Core.Type
import           Facet.Effect.Trace
import           Facet.Elab
import           Facet.Name
import           Facet.Semiring (zero)
import qualified Facet.Surface as S
import           Facet.Syntax
import           GHC.Stack

tvar :: Has (Throw Err :+: Trace) sig m => Q Name -> Synth m TExpr
tvar n = Synth $ trace "tvar" $ views context_ (lookupInContext n) >>= \case
  Just (i, _T) -> pure $ TVar (TFree i) ::: _T
  Nothing      -> do
    q :=: _ ::: _T <- resolveQ n
    instantiate TInst $ TVar (TGlobal q) ::: _T


_Type :: Synth m TExpr
_Type = Synth $ pure $ TType ::: VKType

_Interface :: Synth m TExpr
_Interface = Synth $ pure $ TInterface ::: VKType

_String :: Synth m TExpr
_String = Synth $ pure $ TString ::: VKType


forAll :: Has Trace sig m => Name ::: Check m TExpr -> Check m TExpr -> Synth m TExpr
forAll (n ::: t) b = Synth $ do
  t' <- check (t ::: VKType)
  env <- views context_ toEnv
  subst <- get
  let vt = eval subst env t'
  b' <- Binding n zero vt |- check (b ::: VKType)
  pure $ TForAll n t' b' ::: VKType

(-->) :: Has Trace sig m => Either Name [Check m TExpr] ::: Check m TExpr -> Check m TExpr -> Synth m TExpr
(n ::: a) --> b = Synth $ do
  n' <- traverse (traverse (\ e -> check (e ::: VKInterface))) n
  a' <- check (a ::: VKType)
  b' <- check (b ::: VKType)
  pure $ TArrow n' a' b' ::: VKType

infixr 1 -->


comp :: Has Trace sig m => [Check m TExpr] -> Check m TExpr -> Synth m TExpr
comp s t = Synth $ do
  s' <- traverse (check . (::: VKInterface)) s
  t' <- check (t ::: VKType)
  pure $ TComp s' t' ::: VKType


synthType :: (HasCallStack, Has (Throw Err :+: Trace) sig m) => S.Ann S.Type -> Synth m TExpr
synthType (S.Ann s _ e) = mapSynth (trace "synthType" . setSpan s) $ case e of
  S.TVar n        -> tvar n
  S.KType         -> _Type
  S.KInterface    -> _Interface
  S.TString       -> _String
  S.TForAll n t b -> forAll (n ::: checkType t) (checkType b)
  S.TArrow  n a b -> (map checkInterface <$> n ::: checkType a) --> checkType b
  S.TComp s t     -> comp (map checkInterface s) (checkType t)
  S.TApp f a      -> app TApp (synthType f) (checkType a)

-- | Check a type at a kind.
--
-- NB: while synthesis is possible for all types at present, I reserve the right to change that.
checkType :: (HasCallStack, Has (Throw Err :+: Trace) sig m) => S.Ann S.Type -> Check m TExpr
checkType = switch . synthType

synthInterface :: (HasCallStack, Has (Throw Err :+: Trace) sig m) => S.Ann S.Interface -> Synth m TExpr
synthInterface (S.Ann s _ (S.Interface (S.Ann sh _ h) sp)) = mapSynth (setSpan s) $
  foldl' (app TApp) h' (checkType <$> sp)
  where
  h' = mapSynth (setSpan sh) (tvar h)

checkInterface :: (HasCallStack, Has (Throw Err :+: Trace) sig m) => S.Ann S.Interface -> Check m TExpr
checkInterface = switch . synthInterface
