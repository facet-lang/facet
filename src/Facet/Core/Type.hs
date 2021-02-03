module Facet.Core.Type
( -- * Type variables
  TVar(..)
, Quantity
  -- * Type values
, Type(..)
, global
, free
, metavar
, var
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
  -- * Usage
, Usage(..)
, singleton
, lookupUsage
) where

import           Data.Either (fromLeft)
import           Data.Foldable (foldl')
import           Data.Function ((&))
import qualified Data.IntMap as IntMap
import           Data.Maybe (fromMaybe)
import           Facet.Name
import           Facet.Semiring
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

type Quantity = Few


-- Types

data Type
  = VKType
  | VKInterface
  | VTForAll Name Type (Type -> Type)
  | VTArrow (Either Name [Type]) Quantity Type Type
  | VTNe (TVar Level) (Stack Type) (Stack Type)
  | VTComp [Type] Type
  | VTString


global :: Q Name -> Type
global = var . TGlobal

free :: Level -> Type
free = var . TFree

metavar :: Meta -> Type
metavar = var . TMetavar


var :: TVar Level -> Type
var v = VTNe v Nil Nil


occursIn :: (TVar Level -> Bool) -> Level -> Type -> Bool
occursIn p = go
  where
  go d = \case
    VKType          -> False
    VKInterface     -> False
    VTForAll _ t b  -> go d t || go (succ d) (b (free d))
    VTArrow n _ a b -> any (any (go d)) n || go d a || go d b
    VTComp s t      -> any (go d) s || go d t
    VTNe h ts sp    -> p h || any (go d) ts || any (go d) sp
    VTString        -> False


-- Elimination

($$) :: HasCallStack => Type -> Type -> Type
VTNe h ts es $$ a = VTNe h ts (es :> a)
_            $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (HasCallStack, Foldable t) => Type -> t Type -> Type
($$*) = foldl' ($$)

infixl 9 $$, $$*

($$$) :: HasCallStack => Type -> Type -> Type
VTNe h ts es   $$$ t = VTNe h (ts :> t) es
VTForAll _ _ b $$$ t = b t
_              $$$ _ = error "can’t apply non-neutral/forall type"

($$$*) :: (HasCallStack, Foldable t) => Type -> t Type -> Type
($$$*) = foldl' ($$)

infixl 9 $$$, $$$*


-- Debugging

showType :: Stack ShowP -> Type -> ShowP
showType env = \case
  VKType         -> string "Type"
  VKInterface    -> string "Interface"
  VTForAll n t b -> prec 0 $ brace (name n <+> char ':' <+> setPrec 0 (showType env t)) <+> string "->" <+> setPrec 0 (showType (env :> name n) (b (free (Level (length env)))))
  VTArrow n q t b  -> case n of
    Left  n -> paren (name n <+> char ':' <+> mult q (showType env t)) <+> string "->" <+> setPrec 0 (showType env b)
    Right s -> sig s <+> setPrec 1 (mult q (showType env t)) <+> string "->" <+> setPrec 0 (showType env b)
  VTNe f ts as   -> head f $$* (brace . showType env <$> ts) $$* (setPrec 11 . showType env <$> as)
  VTComp s t     -> brace (sig s <+> showType env t)
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
  | TArrow (Either Name [TExpr]) Quantity TExpr TExpr
  | TComp [TExpr] TExpr
  | TInst TExpr TExpr
  | TApp TExpr TExpr
  deriving (Eq, Ord, Show)


-- Quotation

quote :: Level -> Type -> TExpr
quote d = \case
  VKType          -> TType
  VKInterface     -> TInterface
  VTForAll n t b  -> TForAll n (quote d t) (quote (succ d) (b (free d)))
  VTArrow n q a b -> TArrow (map (quote d) <$> n) q (quote d a) (quote d b)
  VTComp s t      -> TComp (quote d <$> s) (quote d t)
  VTNe n ts sp    -> foldl' (&) (foldl' (&) (TVar (levelToIndex d <$> n)) (flip TInst . quote d <$> ts)) (flip TApp . quote d <$> sp)
  VTString        -> TString

eval :: HasCallStack => Subst -> Stack (Either Type a) -> TExpr -> Type
eval subst = go where
  go env = \case
    TVar (TGlobal n)  -> global n
    TVar (TFree v)    -> fromLeft (error ("term variable at index " <> show v)) (env ! getIndex v)
    TVar (TMetavar m) -> maybe (metavar m) tm (lookupMeta m subst)
    TType             -> VKType
    TInterface        -> VKInterface
    TForAll n t b     -> VTForAll n (go env t) (\ v -> go (env :> Left v) b)
    TArrow n q a b    -> VTArrow (map (go env) <$> n) q (go env a) (go env b)
    TComp s t         -> VTComp (go env <$> s) (go env t)
    TInst f a         -> go env f $$$ go env a
    TApp  f a         -> go env f $$  go env a
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


-- Usage

newtype Usage = Usage (IntMap.IntMap Quantity)

instance Semigroup Usage where
  Usage a <> Usage b = Usage (IntMap.unionWith (<>) a b)

instance Monoid Usage where
  mempty = Usage mempty

instance LeftModule Quantity Usage where
  q ><< Usage a = Usage ((q ><) <$> a)

singleton :: Level -> Quantity -> Usage
singleton (Level i) q = Usage (IntMap.singleton i q)

lookupUsage :: Level -> Usage -> Quantity
lookupUsage (Level i) (Usage a) = fromMaybe zero (IntMap.lookup i a)
