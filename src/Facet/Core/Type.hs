{-# LANGUAGE GADTs #-}
module Facet.Core.Type
( -- * Types
  Type(..)
, N
, P
, global
, free
, metavar
, unComp
, unThunk
, occursIn
  -- * Type expressions
, TExpr(..)
  -- * Shifts
, Shift(..)
  -- * Quotation
, quote
, eval
  -- * Substitution
, Subst(..)
, insert
, lookupMeta
, solveMeta
, declareMeta
, metas
) where

import           Control.Effect.Empty
import           Data.Either (fromLeft)
import           Data.Foldable (foldl')
import qualified Data.IntMap as IntMap
import           Data.Maybe (fromMaybe)
import           Facet.Name
import           Facet.Snoc
import           Facet.Syntax
import           Facet.Usage
import           GHC.Stack
import           Prelude hiding (lookup)

-- Types

data Type u where
  -- Types
  Type :: Type T
  Interface :: Type T
  Arrow' :: Type T -> Type T -> Type T

  -- Negative
  ForAll :: Name -> Type T -> (Type P -> Type N) -> Type N
  Arrow :: Maybe Name -> Quantity -> Type P -> Type N -> Type N
  Comp :: [Type P] -> Type P -> Type N

  -- Positive
  Ne :: Var Meta Level -> Snoc (Type P) -> Type P
  String :: Type P
  Thunk :: Type N -> Type P

instance Shift Type where
  shiftP t = fromMaybe (Comp [] t) (unThunk t)
  shiftN = \case
    Comp [] t -> t
    t         -> Thunk t

global :: Q Name -> Type P
global n = Ne (Global n) Nil

free :: Level -> Type P
free l = Ne (Free l) Nil

metavar :: Meta -> Type P
metavar m = Ne (Metavar m) Nil


unComp :: Has Empty sig m => Type n -> m ([Type P], Type P)
unComp = \case
  Comp sig _T -> pure (sig, _T)
  _T          -> empty

unThunk :: Has Empty sig m => Type p -> m (Type N)
unThunk = \case
  Thunk t -> pure t
  _       -> empty


occursIn :: (Var Meta Level -> Bool) -> Level -> Type u -> Bool
occursIn p = go
  where
  go :: Level -> Type u -> Bool
  go d = \case
    Type          -> False
    Interface     -> False
    Arrow' a b    -> go d a || go d b
    ForAll _ t b  -> go d t || go (succ d) (b (free d))
    Arrow _ _ a b -> go d a || go d b
    Comp s t      -> any (go d) s || go d t
    Ne h sp       -> p h || any (go d) sp
    String        -> False
    Thunk t       -> go d t


-- Elimination

app :: HasCallStack => Type P -> Type P -> Type P
app (Ne h es) a = Ne h (es :> a)
app _         _ = error "can’t apply non-neutral/forall type"


-- Type expressions

data TExpr u where
  TType :: TExpr T
  TInterface :: TExpr T
  TArrow' :: TExpr T -> TExpr T -> TExpr T

  TForAll :: Name -> TExpr T -> TExpr N -> TExpr N
  TArrow :: Maybe Name -> Quantity -> TExpr P -> TExpr N -> TExpr N
  TComp :: [TExpr P] -> TExpr P -> TExpr N

  TVar :: Var Meta Index -> TExpr P
  TApp :: TExpr P -> TExpr P -> TExpr P
  TString :: TExpr P
  TThunk :: TExpr N -> TExpr P

deriving instance Eq   (TExpr u)
deriving instance Ord  (TExpr u)
deriving instance Show (TExpr u)

instance Shift TExpr where
  shiftP = \case
    TThunk t -> t
    t        -> TComp [] t
  shiftN = \case
    TComp [] t -> t
    t          -> TThunk t


-- Shifting

class Shift t where
  shiftP :: t P -> t N
  shiftN :: t N -> t P


-- Quotation

quote :: Level -> Type u -> TExpr u
quote d = \case
  Type          -> TType
  Interface     -> TInterface
  Arrow' a b    -> TArrow' (quote d a) (quote d b)

  ForAll n t b  -> TForAll n (quote d t) (quote (succ d) (b (free d)))
  Arrow n q a b -> TArrow n q (quote d a) (quote d b)
  Comp s t      -> TComp (quote d <$> s) (quote d t)

  Ne n sp       -> foldl' TApp (TVar (levelToIndex d <$> n)) (quote d <$> sp)
  String        -> TString
  Thunk t       -> shiftN (quote d t)

eval :: HasCallStack => Subst (Type P) -> Snoc (Either (Type P) a) -> TExpr u -> Type u
eval subst = go where
  go :: Snoc (Either (Type P) a) -> TExpr u -> Type u
  go env = \case
    TType            -> Type
    TInterface       -> Interface
    TArrow' a b      -> Arrow' (go env a) (go env b)
    TForAll n t b    -> ForAll n (go env t) (\ v -> go (env :> Left v) b)
    TArrow n q a b   -> Arrow n q (go env a) (go env b)
    TComp [] t       -> shiftP (go env t)
    TComp s t        -> Comp (go env <$> s) (go env t)
    TApp f a         -> go env f `app` go env a
    TString          -> String
    TVar (Global n)  -> global n
    TVar (Free v)    -> fromLeft (error ("term variable at index " <> show v)) (env ! getIndex v)
    TVar (Metavar m) -> maybe (metavar m) tm (lookupMeta m subst)
    TThunk t         -> shiftN (go env t)


-- Substitution

newtype Subst t = Subst (IntMap.IntMap (Maybe t ::: t))
  deriving (Monoid, Semigroup)

insert :: Meta -> Maybe t ::: t -> Subst t -> Subst t
insert (Meta i) t (Subst metas) = Subst (IntMap.insert i t metas)

lookupMeta :: Meta -> Subst t -> Maybe (t ::: t)
lookupMeta (Meta i) (Subst metas) = do
  v ::: _T <- IntMap.lookup i metas
  (::: _T) <$> v

solveMeta :: Meta -> t -> Subst t -> Subst t
solveMeta (Meta i) t (Subst metas) = Subst (IntMap.update (\ (_ ::: _T) -> Just (Just t ::: _T)) i metas)

declareMeta :: t -> Subst t -> (Subst t, Meta)
declareMeta _K (Subst metas) = (Subst (IntMap.insert v (Nothing ::: _K) metas), Meta v) where
  v = maybe 0 (succ . fst . fst) (IntMap.maxViewWithKey metas)

metas :: Subst t -> [Meta :=: Maybe t ::: t]
metas (Subst metas) = map (\ (k, v) -> Meta k :=: v) (IntMap.toList metas)
