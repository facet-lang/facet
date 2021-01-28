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
import           Control.Effect.Reader
import           Control.Effect.State
import           Control.Effect.Throw
import           Data.Foldable (foldl', toList)
import           Facet.Context
import           Facet.Core
import           Facet.Effect.Trace
import           Facet.Elab
import           Facet.Name
import           Facet.Span (Pos, Span(start))
import qualified Facet.Surface as S
import           Facet.Syntax
import           GHC.Stack

tvar :: Has (Throw Err :+: Trace) sig m => Q Name -> Synth m TExpr
tvar n = Synth $ trace "tvar" $ gets (lookupInContext n) >>= \case
  Just (i, _T) -> pure $ TVar (Free i) ::: _T
  Nothing      -> do
    q :=: _ ::: _T <- resolveQ n
    instantiate TInst $ TVar (Global q) ::: _T


_Type :: Synth m TExpr
_Type = Synth $ pure $ TType ::: VKType

_Interface :: Synth m TExpr
_Interface = Synth $ pure $ TInterface ::: VKType

_String :: Synth m TExpr
_String = Synth $ pure $ TString ::: VKType


forAll :: Has Trace sig m => Check m (Binding TExpr) -> Check m TExpr -> Synth m TExpr
forAll t b = Synth $ do
  t' <- check (t ::: VKType)
  eval <- gets evalIn
  let vt = fmap eval t'
  b' <- vt |- check (b ::: VKType)
  pure $ TForAll t' b' ::: VKType

(-->) :: Has Trace sig m => Check m TExpr -> Check m TExpr -> Synth m TExpr
a --> b = Synth $ do
  a' <- check (a ::: VKType)
  b' <- check (b ::: VKType)
  pure $ TArrow a' b' ::: VKType


binding :: (HasCallStack, Has (Reader (Sig Type) :+: Throw Err :+: Trace) sig m) => S.Ann S.Binding -> [(Pos, Check m (Binding TExpr))]
binding (S.Ann s _ (S.Binding p n d t)) =
  [ (start s, Check $ \ _T -> setSpan s . trace "binding" $ do
    t' <- check (checkType t ::: _T)
    case d of
      Just d -> do
        d' <- traverse (check . (::: VKInterface) . sig) d
        level <- depth
        e <- askEffectVar
        pure $ Binding p n (TComp (Sig (quote level e) d') t')
      Nothing -> pure $ Binding p n t')
  | n <- maybe [Nothing] (map Just . toList) n ]

sig :: (HasCallStack, Has (Reader (Sig Type) :+: Throw Err :+: Trace) sig m) => S.Ann S.Interface -> Check m TExpr
sig (S.Ann s _ (S.Interface (S.Ann s' _ n) sp)) = Check $ \ _T -> setSpan s . trace "sig" $
  check (switch (foldl' (app TApp) (mapSynth (setSpan s') (tvar n)) (checkType <$> sp)) ::: _T)

comp :: (HasCallStack, Has (Reader (Sig Type) :+: Throw Err :+: Trace) sig m) => S.Ann S.Comp -> Synth m TExpr
comp (S.Ann s _ (S.Comp bs d b)) = Synth $ setSpan s . trace "comp" $ foldr
  (\ t b -> check (snd t ::: VKType) >>= \case
    Binding Im n t -> do
      eval <- gets evalIn
      b' ::: _ <- Binding Im n (eval t) |- b
      pure $ TForAll (Binding Im n t) b' ::: VKType
    Binding Ex _ t -> do
      b' ::: _ <- b
      pure $ TArrow t b' ::: VKType)
  (do
    b' <- check (checkType b ::: VKType)
    case d of
      Just d -> do
        d' <- traverse (check . (::: VKInterface) . sig) d
        level <- depth
        e <- askEffectVar
        pure $ TComp (Sig (quote level e) d') b' ::: VKType
      Nothing -> pure (b' ::: VKType))
  (binding =<< bs)


synthType :: (HasCallStack, Has (Reader (Sig Type) :+: Throw Err :+: Trace) sig m) => S.Ann S.Type -> Synth m TExpr
synthType (S.Ann s _ e) = mapSynth (trace "synthType" . setSpan s) $ case e of
  S.TVar n     -> tvar n
  S.KType      -> _Type
  S.KInterface -> _Interface
  S.TString    -> _String
  S.TComp t    -> comp t
  S.TApp f a   -> app TApp (synthType f) (checkType a)

checkType :: (HasCallStack, Has (Reader (Sig Type) :+: Throw Err :+: Trace) sig m) => S.Ann S.Type -> Check m TExpr
checkType = switch . synthType
