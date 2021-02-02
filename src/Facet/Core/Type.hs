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
  -- ** Debugging
, showType
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

import           Data.Foldable (foldl')
import qualified Data.IntMap as IntMap
import           Facet.Name
import           Facet.Show
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


-- Debugging

showType :: Stack (Endo String) -> Int -> Type -> Endo String
showType env p = \case
  VKType         -> string "Type"
  VKInterface    -> string "Interface"
  VTForAll n t b -> parenIf (p > 0) $ brace (name n <+> char ':' <+> showType env 0 t) <+> string "->" <+> showType (env :> name n) 0 (b (free (Level (length env))))
  VTArrow n t b  -> case n of
    Left  n -> paren (name n <+> char ':' <+> showType env 0 t) <+> string "->" <+> showType env 0 b
    Right s -> sig s <+> showType env 1 t <+> string "->" <+> showType env 0 b
  VTNe (f :$ as) -> parenIf (p > 10) $ foldl' (<+>) (head f) (elim <$> as)
  VTComp s t     -> brace (sig s <+> showType env 0 t)
  VTString       -> string "String"
  where
  sig s = bracket (commaSep (map (showType env 0) s))
  elim = \case
    TEInst t -> brace (showType env 0 t)
    TEApp  t -> showType env 11 t
  head = \case
    TGlobal q  -> qname q
    TFree v    -> env ! getIndex (levelToIndex (Level (length env)) v)
    TMetavar m -> char '?' <> string (show (getMeta m))


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
    TVar (TMetavar m) -> maybe (metavar m) tm (lookupMeta m subst)
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

insert :: Meta -> Maybe Type ::: Type -> Subst -> Subst
insert (Meta i) t (Subst metas) = Subst (IntMap.insert i t metas)

lookupMeta :: Meta -> Subst -> Maybe (Type ::: Type)
lookupMeta (Meta i) (Subst metas) = do
  v ::: _T <- IntMap.lookup i metas
  (::: _T) <$> v

solveMeta :: Meta -> Type -> Subst -> Subst
solveMeta (Meta i) t (Subst metas) = Subst (IntMap.update (\ (_ ::: _T) -> Just (Just t ::: _T)) i metas)

declareMeta :: Type -> Subst -> (Subst, Meta)
declareMeta _K (Subst metas) = (Subst (IntMap.insert v (Nothing ::: _K) metas), Meta v) where
  v = maybe 0 (succ . fst . fst) (IntMap.maxViewWithKey metas)

metas :: Subst -> [Meta :=: Maybe Type ::: Type]
metas (Subst metas) = map (\ (k, v) -> Meta k :=: v) (IntMap.toList metas)
