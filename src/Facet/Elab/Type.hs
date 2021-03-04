{-# LANGUAGE OverloadedStrings #-}
module Facet.Elab.Type
( -- * Types
  _Type
, _Interface
, _String
, forAll
, elabKind
, elabType
  -- * Judgements
, checkIsType
, IsType(..)
, mapIsType
) where

import           Control.Algebra
import           Control.Effect.Lens (views)
import           Control.Effect.State
import           Control.Effect.Throw
import           Control.Effect.Writer
import           Data.Bifunctor (first)
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
import           Facet.Usage (Usage)
import           GHC.Stack

var :: (HasCallStack, Has (Throw Err) sig m) => (Var Meta Index -> a) -> QName -> IsType m a
var mk n = IsType $ views context_ (lookupInContext n) >>= \case
  Just (i, q, _T) -> use i q $> (mk (Free i) ::: _T)
  _               -> do
    q :=: d <- resolveQ n
    _T <- case d of
      DData      _ _K -> pure _K
      DInterface _ _K -> pure _K
      _               -> freeVariable q
    pure $ mk (Global q) ::: _T


_Type :: IsType m TExpr
_Type = IsType $ pure $ TType ::: Type

_Interface :: IsType m TExpr
_Interface = IsType $ pure $ TInterface ::: Type

_String :: IsType m (Pos TExpr)
_String = IsType $ pure $ stringT ::: Type


forAll :: (HasCallStack, Has (Throw Err) sig m) => Name ::: IsType m TExpr -> IsType m (Pos TExpr) -> IsType m (Pos TExpr)
forAll (n ::: t) b = IsType $ do
  t' <- checkIsType (t ::: Type)
  env <- views context_ toEnv
  subst <- get
  let vt = eval subst (Left <$> env) t'
  b' <- Binding n zero vt |- checkIsType (b ::: Type)
  pure $ thunkT (forAllT n t' (compT [] b')) ::: Type

arrow :: (HasCallStack, Has (Throw Err) sig m) => (a -> b -> c) -> IsType m a -> IsType m b -> IsType m c
arrow mk a b = IsType $ do
  a' <- checkIsType (a ::: Type)
  b' <- checkIsType (b ::: Type)
  pure $ mk a' b' ::: Type

function :: (HasCallStack, Has (Throw Err) sig m) => Maybe Name ::: (Quantity, IsType m (Pos TExpr)) -> IsType m (Pos TExpr) -> IsType m (Pos TExpr)
function (n ::: (q, a)) = arrow (\ a b -> thunkT (arrowT n q a (compT [] b))) a


comp :: (HasCallStack, Has (Throw Err) sig m) => [IsType m (Interface TExpr)] -> IsType m (Pos TExpr) -> IsType m (Neg TExpr)
comp s t = IsType $ do
  s' <- traverse (checkIsType . (::: Interface)) s
  t' <- checkIsType (t ::: Type)
  pure $ compT s' t' ::: Type

app :: (HasCallStack, Has (Throw Err) sig m) => (a -> b -> c) -> IsType m a -> IsType m b -> IsType m c
app mk f a = IsType $ do
  f' ::: _F <- isType f
  -- FIXME: assert that the usage is zero.
  (_ ::: (q, _A), _B) <- expectFunction "in application" _F
  a' <- censor @Usage (q ><<) $ checkIsType (a ::: _A)
  pure $ mk f' a' ::: _B


elabKind :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> IsType m TExpr
elabKind (S.Ann s _ e) = mapIsType (pushSpan s) $ case e of
  S.TArrow  n q a b -> arrow (TArrow n (maybe Many interpretMul q)) (elabKind a) (elabKind b)
  S.TApp f a        -> app TApp (elabKind f) (elabKind a)
  S.TVar n          -> var TVar n
  S.KType           -> _Type
  S.KInterface      -> _Interface
  S.TComp{}         -> nope
  S.TForAll{}       -> nope
  S.TString         -> nope
  where
  nope = IsType $ couldNotSynthesize (show e <> " at the kind level")


elabType :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Type -> IsType m (Pos TExpr)
elabType (S.Ann s _ e) = mapIsType (pushSpan s) $ case e of
  S.TForAll n t b   -> forAll (n ::: elabKind t) (elabType b)
  S.TArrow  n q a b -> function (n ::: (maybe Many interpretMul q, elabType a)) (elabType b)
  S.TComp s t       -> thunkT <$> comp (map synthInterface s) (elabType t)
  S.TApp f a        -> app appT (elabType f) (elabType a)
  S.TVar n          -> var varT n
  S.TString         -> _String
  S.KType           -> nope
  S.KInterface      -> nope
  where
  nope = IsType $ couldNotSynthesize (show e <> " at the type level")


interpretMul :: S.Mul -> Few
interpretMul = \case
  S.Zero -> zero
  S.One  -> one


synthInterface :: (HasCallStack, Has (Throw Err) sig m) => S.Ann S.Interface -> IsType m (Interface TExpr)
synthInterface (S.Ann s _ (S.Interface (S.Ann sh _ h) sp)) = mapIsType (pushSpan s) . fmap IInterface $
  foldl' (app TApp) (mapIsType (pushSpan sh) (var TVar h)) (elabKind <$> sp)


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
