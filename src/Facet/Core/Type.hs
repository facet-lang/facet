module Facet.Core.Type
( -- * Type variables
  TVar(..)
  -- * Type values
, Type(..)
, TElim(..)
, global
, free
, metavar
, var
, occursIn
  -- ** Elimination
, ($$)
, ($$*)
  -- * Type expressions
, TExpr(..)
  -- * Quotation
, quote
, eval
  -- * Substitution
, Subst(..)
, lookup
) where

import           Data.Foldable (foldl')
import qualified Data.IntMap as IntMap
import           Data.Maybe (fromMaybe)
import           Facet.Name
import           Facet.Stack
import           Facet.Syntax
import           GHC.Stack
import           Prelude hiding (lookup)

-- Variables

data TVar a
  = TGlobal (Q Name) -- ^ Global variables, considered equal by 'Q' 'Name'.
  | TFree a
  | TMetavar Meta
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)


-- Types

data Type
  = VKType
  | VKInterface
  | VTForAll Name Type (Type -> Type)
  | VTArrow (Either Name [Type]) Type Type
  | VTNe (TVar Level :$ TElim)
  | VTComp [Type] Type
  | VTString

data TElim
  = TEInst Type
  | TEApp Type


global :: Q Name -> Type
global = var . TGlobal

free :: Level -> Type
free = var . TFree

metavar :: Meta -> Type
metavar = var . TMetavar


var :: TVar Level -> Type
var = VTNe . (:$ Nil)


occursIn :: (TVar Level -> Bool) -> Level -> Type -> Bool
occursIn p = go
  where
  go d = \case
    VKType         -> False
    VKInterface    -> False
    VTForAll _ t b -> go d t || go (succ d) (b (free d))
    VTArrow n a b  -> any (any (go d)) n || go d a || go d b
    VTComp s t     -> any (go d) s || go d t
    VTNe (h :$ sp) -> p h || any (elim d) sp
    VTString       -> False

  elim d = \case
    TEInst t -> go d t
    TEApp  t -> go d t


-- Elimination

($$) :: HasCallStack => Type -> TElim -> Type
VTNe (h :$ es) $$ a = VTNe (h :$ (es :> a))
VTForAll _ _ b $$ a = b (case a of
  TEInst a -> a
  TEApp  a -> a) -- FIXME: technically this should only ever be TEInst
_              $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (HasCallStack, Foldable t) => Type -> t TElim -> Type
($$*) = foldl' ($$)

infixl 9 $$, $$*


-- Type expressions

data TExpr
  = TVar (TVar Index)
  | TType
  | TInterface
  | TString
  | TForAll Name TExpr TExpr
  | TArrow (Either Name [TExpr]) TExpr TExpr
  | TComp [TExpr] TExpr
  | TInst TExpr TExpr
  | TApp TExpr TExpr
  deriving (Eq, Ord, Show)


-- Quotation

quote :: Level -> Type -> TExpr
quote d = \case
  VKType         -> TType
  VKInterface    -> TInterface
  VTForAll n t b -> TForAll n (quote d t) (quote (succ d) (b (free d)))
  VTArrow n a b  -> TArrow (map (quote d) <$> n) (quote d a) (quote d b)
  VTComp s t     -> TComp (quote d <$> s) (quote d t)
  VTNe (n :$ sp) -> foldl' (\ head -> \case
    TEInst a -> TInst head (quote d a)
    TEApp  a -> TApp head (quote d a)) (TVar (levelToIndex d <$> n)) sp
  VTString       -> TString

eval :: HasCallStack => Subst -> Stack Type -> TExpr -> Type
eval subst = go where
  go env = \case
    TVar (TGlobal n)  -> global n
    TVar (TFree v)    -> env ! getIndex v
    TVar (TMetavar m) -> fromMaybe (metavar m) (tm =<< lookup m subst)
    TType             -> VKType
    TInterface        -> VKInterface
    TForAll n t b     -> VTForAll n (go env t) (\ v -> go (env :> v) b)
    TArrow n a b      -> VTArrow (map (go env) <$> n) (go env a) (go env b)
    TComp s t         -> VTComp (go env <$> s) (go env t)
    TInst f a         -> go env f $$ TEInst (go env a)
    TApp  f a         -> go env f $$ TEApp (go env a)
    TString           -> VTString


-- Substitution

newtype Subst = Subst (IntMap.IntMap (Maybe Type ::: Type))
  deriving (Monoid, Semigroup)

lookup :: Meta -> Subst -> Maybe (Maybe Type ::: Type)
lookup (Meta i) (Subst metas) = IntMap.lookup i metas
