module Facet.Core.Type
( -- * Kinds
  Kind(..)
  -- * Types
, Interface(..)
, Signature(..)
, fromInterfaces
, singleton
, interfaces
, mapSignature
, Type(..)
, global
, free
, metavar
, unNeutral
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
) where

import           Control.Effect.Empty
import           Data.Foldable (foldl')
import           Data.Function (on, (&))
import           Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import           Facet.Name
import           Facet.Snoc
import           Facet.Subst
import           Facet.Syntax
import           Facet.Usage hiding (singleton)
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

newtype Signature a = Signature { getSignature :: Set.Set (Interface a) }
  deriving (Eq, Foldable, Monoid, Ord, Semigroup, Show)

fromInterfaces :: Ord a => [Interface a] -> Signature a
fromInterfaces = Signature . Set.fromList

singleton :: Interface a -> Signature a
singleton = Signature . Set.singleton

interfaces :: Signature a -> [Interface a]
interfaces = Set.toList . getSignature

mapSignature :: Ord b => (a -> b) -> Signature a -> Signature b
mapSignature f = Signature . Set.map (fmap f) . getSignature


data Type
  = VString
  | VForAll Name Kind (Type -> Type)
  | VArrow (Maybe Name) Quantity Type Type
  | VNe (Var (Either Meta Level)) (Snoc Type)
  | VComp (Signature Type) Type

instance Eq Type where
  (==) = (==) `on` quote 0

instance Ord Type where
  compare = compare `on` quote 0


global :: RName -> Type
global = var . Global

free :: Level -> Type
free = var . Free . Right

metavar :: Meta -> Type
metavar = var . Free . Left


var :: Var (Either Meta Level) -> Type
var v = VNe v Nil


unNeutral :: Has Empty sig m => Type -> m (Var (Either Meta Level), Snoc Type)
unNeutral = \case
  VNe h sp -> pure (h, sp)
  _        -> empty

unComp :: Has Empty sig m => Type -> m (Signature Type, Type)
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


occursIn :: Meta -> Level -> Type -> Bool
occursIn p = go
  where
  go d = \case
    VForAll _ _ b  -> go (succ d) (b (free d))
    VArrow _ _ a b -> go d a || go d b
    VComp s t      -> any (go d) s || go d t
    VNe h sp       -> any (either (== p) (const False)) h || any (go d) sp
    VString        -> False


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
  | TComp (Signature TExpr) TExpr
  | TApp TExpr TExpr
  deriving (Eq, Ord, Show)


-- Quotation

quote :: Level -> Type -> TExpr
quote d = \case
  VString        -> TString
  VForAll n t b  -> TForAll n t (quote (succ d) (b (free d)))
  VArrow n q a b -> TArrow n q (quote d a) (quote d b)
  VComp s t      -> TComp (mapSignature (quote d) s) (quote d t)
  VNe n sp       -> foldl' (&) (TVar (fmap (levelToIndex d) <$> n)) (flip TApp . quote d <$> sp)

eval :: HasCallStack => Subst Type -> Level -> TExpr -> Type
eval subst d = go (fromList (map free [0..pred d])) where
  go env = \case
    TString               -> VString
    TVar (Global n)       -> global n
    TVar (Free (Right v)) -> env ! getIndex v
    TVar (Free (Left m))  -> fromMaybe (metavar m) (lookupMeta m subst)
    TForAll n t b         -> VForAll n t (\ v -> go (env :> v) b)
    TArrow n q a b        -> VArrow n q (go env a) (go env b)
    TComp s t             -> VComp (mapSignature (go env) s) (go env t)
    TApp  f a             -> go env f $$  go env a

apply :: HasCallStack => Subst Type -> Level -> Type -> Type
apply subst d = eval subst d . quote d
