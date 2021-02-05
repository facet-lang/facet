module Facet.Core.Type
( -- * Variables
  TVar(..)
  -- * Types
, VType(..)
, CType(..)
, global
, free
, metavar
, var
, unRet
, occursIn
  -- ** Elimination
, ($$)
, ($$*)
, ($$$)
, ($$$*)
  -- ** Debugging
, showType
  -- * Type expressions
, TExpr(..)
, VTExpr(..)
, CTExpr(..)
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
import           Data.Function ((&))
import qualified Data.IntMap as IntMap
import           Facet.Name
import           Facet.Semiring
import           Facet.Show
import           Facet.Stack
import           Facet.Syntax
import           Facet.Usage
import           GHC.Stack
import           Prelude hiding (lookup)

-- Variables

data TVar a
  = TGlobal (Q Name) -- ^ Global variables, considered equal by 'Q' 'Name'.
  | TFree a
  | TMetavar Meta
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)


-- Types

data VType
  = VKType
  | VKInterface
  | VTForAll Name VType (VType -> VType)
  | VTArrow (Maybe Name) Quantity VType VType
  | VTNe (TVar Level) (Stack VType) (Stack VType)
  | VTSusp VType
  | VTRet [VType] VType
  | VTString

data CType
  = CForAll Name CType (CType -> CType)
  | CArrow (Maybe Name) Quantity CType CType
  | CNe (TVar Level) (Stack CType) (Stack CType)
  | CRet [CType] VType


global :: Q Name -> VType
global = var . TGlobal

free :: Level -> VType
free = var . TFree

metavar :: Meta -> VType
metavar = var . TMetavar


var :: TVar Level -> VType
var v = VTNe v Nil Nil


unRet :: Has Empty sig m => VType -> m ([VType], VType)
unRet = \case
  VTRet sig _T -> pure (sig, _T)
  _T           -> empty


occursIn :: (TVar Level -> Bool) -> Level -> VType -> Bool
occursIn p = go
  where
  go d = \case
    VKType          -> False
    VKInterface     -> False
    VTForAll _ t b  -> go d t || go (succ d) (b (free d))
    VTArrow _ _ a b -> go d a || go d b
    VTSusp t        -> go d t
    VTRet s t       -> any (go d) s || go d t
    VTNe h ts sp    -> p h || any (go d) ts || any (go d) sp
    VTString        -> False


-- Elimination

($$) :: HasCallStack => VType -> VType -> VType
VTNe h ts es $$ a = VTNe h ts (es :> a)
_            $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (HasCallStack, Foldable t) => VType -> t VType -> VType
($$*) = foldl' ($$)

infixl 9 $$, $$*

($$$) :: HasCallStack => VType -> VType -> VType
VTNe h ts es   $$$ t = VTNe h (ts :> t) es
VTForAll _ _ b $$$ t = b t
_              $$$ _ = error "can’t apply non-neutral/forall type"

($$$*) :: (HasCallStack, Foldable t) => VType -> t VType -> VType
($$$*) = foldl' ($$)

infixl 9 $$$, $$$*


-- Debugging

showType :: Stack ShowP -> VType -> ShowP
showType env = \case
  VKType         -> string "VType"
  VKInterface    -> string "Interface"
  VTForAll n t b -> prec 0 $ brace (name n <+> char ':' <+> setPrec 0 (showType env t)) <+> string "->" <+> setPrec 0 (showType (env :> name n) (b (free (Level (length env)))))
  VTArrow n q t b  -> case n of
    Just  n -> paren (name n <+> char ':' <+> mult q (showType env t)) <+> string "->" <+> setPrec 0 (showType env b)
    Nothing -> setPrec 1 (mult q (showType env t)) <+> string "->" <+> setPrec 0 (showType env b)
  VTNe f ts as   -> head f $$* (brace . showType env <$> ts) $$* (setPrec 11 . showType env <$> as)
  VTSusp t       -> brace (showType env t)
  VTRet s t      -> sig s <+> showType env t
  VTString       -> string "String"
  where
  sig s = bracket (commaSep (map (showType env) s))
  ($$*) = foldl' (\ f a -> prec 10 (f <+> a))
  infixl 9 $$*
  head = \case
    TGlobal q  -> qname q
    TFree v    -> env ! getIndex (levelToIndex (Level (length env)) v)
    TMetavar m -> char '?' <> string (show (getMeta m))
  mult q = if
    | q == zero -> (char '0' <+>)
    | q == one  -> (char '1' <+>)
    | otherwise -> id


-- Type expressions

data TExpr
  = TVar (TVar Index)
  | TType
  | TInterface
  | TString
  | TForAll Name TExpr TExpr
  | TArrow (Maybe Name) Quantity TExpr TExpr
  | TSusp TExpr
  | TRet [TExpr] TExpr
  | TInst TExpr TExpr
  | TApp TExpr TExpr
  deriving (Eq, Ord, Show)

data VTExpr
  = VEType
  | VEInterface
  | VEString
  | VESusp CTExpr
  deriving (Eq, Ord, Show)

data CTExpr
  = CEVar (TVar Index)
  | CEForAll Name CTExpr CTExpr
  | CEArrow (Maybe Name) Quantity CTExpr CTExpr
  | CEInst CTExpr CTExpr
  | CEApp CTExpr CTExpr
  | CERet [CTExpr] VTExpr
  deriving (Eq, Ord, Show)


-- Quotation

quote :: Level -> VType -> TExpr
quote d = \case
  VKType          -> TType
  VKInterface     -> TInterface
  VTForAll n t b  -> TForAll n (quote d t) (quote (succ d) (b (free d)))
  VTArrow n q a b -> TArrow n q (quote d a) (quote d b)
  VTSusp t        -> TSusp (quote d t)
  VTRet s t       -> TRet (quote d <$> s) (quote d t)
  VTNe n ts sp    -> foldl' (&) (foldl' (&) (TVar (levelToIndex d <$> n)) (flip TInst . quote d <$> ts)) (flip TApp . quote d <$> sp)
  VTString        -> TString

eval :: HasCallStack => Subst -> Stack (Either VType a) -> TExpr -> VType
eval subst = go where
  go env = \case
    TVar (TGlobal n)  -> global n
    TVar (TFree v)    -> fromLeft (error ("term variable at index " <> show v)) (env ! getIndex v)
    TVar (TMetavar m) -> maybe (metavar m) tm (lookupMeta m subst)
    TType             -> VKType
    TInterface        -> VKInterface
    TForAll n t b     -> VTForAll n (go env t) (\ v -> go (env :> Left v) b)
    TArrow n q a b    -> VTArrow n q (go env a) (go env b)
    TSusp t           -> VTSusp (go env t)
    TRet s t          -> VTRet (go env <$> s) (go env t)
    TInst f a         -> go env f $$$ go env a
    TApp  f a         -> go env f $$  go env a
    TString           -> VTString


-- Substitution

newtype Subst = Subst (IntMap.IntMap (Maybe VType ::: VType))
  deriving (Monoid, Semigroup)

insert :: Meta -> Maybe VType ::: VType -> Subst -> Subst
insert (Meta i) t (Subst metas) = Subst (IntMap.insert i t metas)

lookupMeta :: Meta -> Subst -> Maybe (VType ::: VType)
lookupMeta (Meta i) (Subst metas) = do
  v ::: _T <- IntMap.lookup i metas
  (::: _T) <$> v

solveMeta :: Meta -> VType -> Subst -> Subst
solveMeta (Meta i) t (Subst metas) = Subst (IntMap.update (\ (_ ::: _T) -> Just (Just t ::: _T)) i metas)

declareMeta :: VType -> Subst -> (Subst, Meta)
declareMeta _K (Subst metas) = (Subst (IntMap.insert v (Nothing ::: _K) metas), Meta v) where
  v = maybe 0 (succ . fst . fst) (IntMap.maxViewWithKey metas)

metas :: Subst -> [Meta :=: Maybe VType ::: VType]
metas (Subst metas) = map (\ (k, v) -> Meta k :=: v) (IntMap.toList metas)
