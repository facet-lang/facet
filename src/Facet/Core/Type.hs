{-# LANGUAGE GADTs #-}
module Facet.Core.Type
( -- * Types
  Type(..)
, C
, V
, global
, free
, metavar
, unComp
, unThunk
, occursIn
  -- * Type expressions
, TExpr(..)
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
import           Facet.Name
import           Facet.Snoc
import           Facet.Syntax
import           Facet.Usage
import           GHC.Stack
import           Prelude hiding (lookup)

-- Types

data Type u where
  ForAll :: Name -> Type V -> (Type V -> Type C) -> Type C
  Arrow :: Maybe Name -> Quantity -> Type V -> Type C -> Type C
  Comp :: [Type V] -> Type V -> Type C
  Ne :: Var Meta Level -> Snoc (Type V) -> Snoc (Type V) -> Type C

  Var :: Var Meta Level -> Type V
  Type :: Type V
  Interface :: Type V
  String :: Type V
  Thunk :: Type C -> Type V


global :: Q Name -> Type C
global = var . Global

free :: Level -> Type C
free = var . Free

metavar :: Meta -> Type C
metavar = var . Metavar


var :: Var Meta Level -> Type C
var v = Ne v Nil Nil


unComp :: Has Empty sig m => Type C -> m ([Type V], Type V)
unComp = \case
  Comp sig _T -> pure (sig, _T)
  _T          -> empty

unThunk :: Has Empty sig m => Type V -> m (Type C)
unThunk = \case
  Thunk t -> pure t
  _       -> empty


occursIn :: (Var Meta Level -> Bool) -> Level -> Type u -> Bool
occursIn p = go
  where
  go :: Level -> Type u -> Bool
  go d = \case
    Var v         -> p v
    Type          -> False
    Interface     -> False
    ForAll _ t b  -> go d t || go (succ d) (b (Var (Free d)))
    Arrow _ _ a b -> go d a || go d b
    Comp s t      -> any (go d) s || go d t
    Ne h ts sp    -> p h || any (go d) ts || any (go d) sp
    String        -> False
    Thunk t       -> go d t


-- Elimination

app :: HasCallStack => Type C -> Type V -> Type C
app (Ne h ts es) a = Ne h ts (es :> a)
app _            _ = error "can’t apply non-neutral/forall type"

inst :: HasCallStack => Type C -> Type V -> Type C
inst (Ne h ts es)   t = Ne h (ts :> t) es
inst (ForAll _ _ b) t = b t
inst _              _ = error "can’t apply non-neutral/forall type"


-- Type expressions

data TExpr u where
  TForAll :: Name -> TExpr V -> TExpr C -> TExpr C
  TArrow :: Maybe Name -> Quantity -> TExpr V -> TExpr C -> TExpr C
  TComp :: [TExpr V] -> TExpr V -> TExpr C
  TInst :: TExpr C -> TExpr V -> TExpr C
  TApp :: TExpr C -> TExpr V -> TExpr C
  TType :: TExpr V
  TInterface :: TExpr V
  TString :: TExpr V
  TVar :: Var Meta Index -> TExpr V
  TThunk :: TExpr C -> TExpr V

deriving instance Eq   (TExpr u)
deriving instance Ord  (TExpr u)
deriving instance Show (TExpr u)


-- Quotation

quote :: Level -> Type u -> TExpr u
quote d = \case
  ForAll n t b  -> TForAll n (quote d t) (quote (succ d) (b (Var (Free d))))
  Arrow n q a b -> TArrow n q (quote d a) (quote d b)
  Comp s t      -> TComp (quote d <$> s) (quote d t)
  Ne n ts sp    -> foldl' TApp (foldl' TInst (TComp [] (TVar (levelToIndex d <$> n))) (quote d <$> ts)) (quote d <$> sp)
  Var n         -> TVar (levelToIndex d <$> n)
  Type          -> TType
  Interface     -> TInterface
  String        -> TString
  Thunk t       -> TThunk (quote d t)

eval :: HasCallStack => Subst (Type V) -> Snoc (Either (Type V) a) -> TExpr u -> Type u
eval subst = go where
  go :: Snoc (Either (Type V) a) -> TExpr u -> Type u
  go env = \case
    TForAll n t b    -> ForAll n (go env t) (\ v -> go (env :> Left v) b)
    TArrow n q a b   -> Arrow n q (eval subst env a) (go env b)
    TComp s t        -> Comp (go env <$> s) (go env t)
    TInst f a        -> go env f `inst` eval subst env a
    TApp  f a        -> go env f `app`  eval subst env a
    TType            -> Type
    TInterface       -> Interface
    TString          -> String
    TVar (Global n)  -> Var (Global n)
    TVar (Free v)    -> fromLeft (error ("term variable at index " <> show v)) (env ! getIndex v)
    TVar (Metavar m) -> maybe (Var (Metavar m)) tm (lookupMeta m subst)
    TThunk t         -> Thunk (go env t)


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
