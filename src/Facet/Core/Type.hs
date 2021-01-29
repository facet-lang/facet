module Facet.Core.Type
( -- * Type values
  Type(..)
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
) where

import           Data.Foldable (foldl')
import qualified Data.IntMap as IntMap
import           Data.Maybe (fromMaybe)
import           Facet.Core
import           Facet.Name
import           Facet.Stack
import           Facet.Syntax
import           GHC.Stack

-- Types

data Type
  = VKType
  | VKInterface
  | VTForAll Name Type (Type -> Type)
  | VTArrow (Either Name [Type]) Type Type
  | VTNe (Var Level :$ TElim)
  | VTComp [Type] Type
  | VTString

data TElim
  = TEInst Type
  | TEApp Type


global :: Q Name -> Type
global = var . Global

free :: Level -> Type
free = var . Free

metavar :: Meta -> Type
metavar = var . Metavar


var :: Var Level -> Type
var = VTNe . (:$ Nil)


occursIn :: (Var Level -> Bool) -> Level -> Type -> Bool
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
  = TVar (Var Index)
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

eval :: HasCallStack => IntMap.IntMap Type -> Stack Type -> TExpr -> Type
eval subst = go where
  go env = \case
    TVar v        -> unVar global ((env !) . getIndex) (\ m -> fromMaybe (metavar m) (IntMap.lookup (getMeta m) subst)) v
    TType         -> VKType
    TInterface    -> VKInterface
    TForAll n t b -> VTForAll n (go env t) (\ v -> go (env :> v) b)
    TArrow n a b  -> VTArrow (map (go env) <$> n) (go env a) (go env b)
    TComp s t     -> VTComp (go env <$> s) (go env t)
    TInst f a     -> go env f $$ TEInst (go env a)
    TApp  f a     -> go env f $$ TEApp (go env a)
    TString       -> VTString
