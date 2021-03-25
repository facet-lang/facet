module Facet.Core.Type
( -- * Kinds
  Kind(..)
  -- * Types
, Interface(..)
, Type(..)
, global
, free
, metavar
, unComp
, Subject(..)
, subjectType
, occursIn
  -- ** Elimination
, ($$)
, ($$*)
  -- * Type expressions
, TExpr(..)
  -- * Quotation
, quote
, eval
, apply
  -- * Substitution
, Subst(..)
, insert
, lookupMeta
, solveMeta
, declareMeta
, metas
) where

import           Control.Effect.Empty
import           Data.Foldable (foldl')
import           Data.Function ((&))
import qualified Data.IntMap as IntMap
import           Facet.Name
import           Facet.Snoc
import           Facet.Syntax
import           Facet.Usage
import           GHC.Stack
import           Prelude hiding (lookup)

-- Kinds

data Kind
  = KType
  | KInterface
  | KArrow (Maybe Name) Kind Kind
  deriving (Eq, Ord, Show)


-- Types

data Interface a = Interface RName (Snoc a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Type
  = VString
  | VForAll Name Kind (Type -> Type)
  | VArrow (Maybe Name) Quantity Type Type
  | VNe (Var (Either Meta Level)) (Snoc Type)
  | VComp [Interface Type] Type


global :: RName -> Type
global = var . Global

free :: Level -> Type
free = var . Free . Right

metavar :: Meta -> Type
metavar = var . Free . Left


var :: Var (Either Meta Level) -> Type
var v = VNe v Nil


unComp :: Has Empty sig m => Type -> m ([Interface Type], Type)
unComp = \case
  VComp sig _T -> pure (sig, _T)
  _T           -> empty


data Subject
  = SK Kind
  | ST Type

subjectType :: Subject -> Maybe Type
subjectType = \case
  SK _K -> empty
  ST _T -> pure _T


occursIn :: (Var (Either Meta Level) -> Bool) -> Level -> Type -> Bool
occursIn p = go
  where
  go d = \case
    VForAll _ _ b  -> go (succ d) (b (free d))
    VArrow _ _ a b -> go d a || go d b
    VComp s t      -> any (goI d) s || go d t
    VNe h sp       -> p h || any (go d) sp
    VString        -> False
  goI d (Interface h sp) = p (Global h) || any (go d) sp


-- Elimination

($$) :: HasCallStack => Type -> Type -> Type
VNe h es $$ a = VNe h (es :> a)
_        $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (HasCallStack, Foldable t) => Type -> t Type -> Type
($$*) = foldl' ($$)

infixl 9 $$, $$*


-- Type expressions

data TExpr
  = TString
  | TVar (Var (Either Meta Index))
  | TForAll Name Kind TExpr
  | TArrow (Maybe Name) Quantity TExpr TExpr
  | TComp [Interface TExpr] TExpr
  | TApp TExpr TExpr
  deriving (Eq, Ord, Show)


-- Quotation

quote :: Level -> Type -> TExpr
quote d = \case
  VString        -> TString
  VForAll n t b  -> TForAll n t (quote (succ d) (b (free d)))
  VArrow n q a b -> TArrow n q (quote d a) (quote d b)
  VComp s t      -> TComp (fmap (quote d) <$> s) (quote d t)
  VNe n sp       -> foldl' (&) (TVar (fmap (levelToIndex d) <$> n)) (flip TApp . quote d <$> sp)

eval :: HasCallStack => Subst -> Snoc Type -> TExpr -> Type
eval subst = go where
  go env = \case
    TString               -> VString
    TVar (Global n)       -> global n
    TVar (Free (Right v)) -> env ! getIndex v
    TVar (Free (Left m))  -> maybe (metavar m) tm (lookupMeta m subst)
    TForAll n t b         -> VForAll n t (\ v -> go (env :> v) b)
    TArrow n q a b        -> VArrow n q (go env a) (go env b)
    TComp s t             -> VComp (fmap (go env) <$> s) (go env t)
    TApp  f a             -> go env f $$  go env a

apply :: HasCallStack => Subst -> Snoc Type -> Type -> Type
apply subst env = eval subst env . quote (Level (length env))


-- Substitution

newtype Subst = Subst (IntMap.IntMap (Maybe Type ::: Kind))
  deriving (Monoid, Semigroup)

insert :: Meta -> Maybe Type ::: Kind -> Subst -> Subst
insert (Meta i) t (Subst metas) = Subst (IntMap.insert i t metas)

lookupMeta :: Meta -> Subst -> Maybe (Type ::: Kind)
lookupMeta (Meta i) (Subst metas) = do
  v ::: _T <- IntMap.lookup i metas
  (::: _T) <$> v

solveMeta :: Meta -> Type -> Subst -> Subst
solveMeta (Meta i) t (Subst metas) = Subst (IntMap.update (\ (_ ::: _T) -> Just (Just t ::: _T)) i metas)

declareMeta :: Kind -> Subst -> (Subst, Meta)
declareMeta _K (Subst metas) = (Subst (IntMap.insert v (Nothing ::: _K) metas), Meta v) where
  v = maybe 0 (succ . fst . fst) (IntMap.maxViewWithKey metas)

metas :: Subst -> [Meta :=: Maybe Type ::: Kind]
metas (Subst metas) = map (\ (k, v) -> Meta k :=: v) (IntMap.toList metas)
