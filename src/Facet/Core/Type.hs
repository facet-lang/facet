{-# LANGUAGE GADTs #-}
module Facet.Core.Type
( -- * Types
  Type(..)
, C
, V
, Type'
, global
, free
, metavar
, unComp
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
, TExpr'(..)
  -- * Quotation
, quote
, quote'
, eval
, eval'
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
import           Facet.Snoc
import           Facet.Syntax
import           Facet.Usage
import           GHC.Stack
import           Prelude hiding (lookup)

-- Types

data Type
  = VType
  | VInterface
  | VString
  | VForAll Name Type (Type -> Type)
  | VArrow (Maybe Name) Quantity Type Type
  | VNe (Var Meta Level) (Snoc Type) (Snoc Type)
  | VComp [Type] Type
  | VF Type
  | VThunk Type


data Type' u where
  ForAll :: Name -> Type' V -> (Type' V -> Type' C) -> Type' C
  Arrow :: Maybe Name -> Quantity -> Type' V -> Type' C -> Type' C
  Comp :: [Type' V] -> Type' V -> Type' C -- FIXME: I think this should probably be combined with F and Ne
  Ne :: Var Meta Level -> Snoc (Type' V) -> Snoc (Type' V) -> Type' C
  F :: Type' V -> Type' C

  Var :: Var Meta Level -> Type' V
  Type :: Type' V
  Interface :: Type' V
  String :: Type' V
  Thunk :: Type' C -> Type' V


global :: Q Name -> Type
global = var . Global

free :: Level -> Type
free = var . Free

metavar :: Meta -> Type
metavar = var . Metavar


var :: Var Meta Level -> Type
var v = VNe v Nil Nil


unComp :: Has Empty sig m => Type -> m ([Type], Type)
unComp = \case
  VComp sig _T -> pure (sig, _T)
  _T           -> empty


occursIn :: (Var Meta Level -> Bool) -> Level -> Type -> Bool
occursIn p = go
  where
  go d = \case
    VType          -> False
    VInterface     -> False
    VForAll _ t b  -> go d t || go (succ d) (b (free d))
    VArrow _ _ a b -> go d a || go d b
    VComp s t      -> any (go d) s || go d t
    VNe h ts sp    -> p h || any (go d) ts || any (go d) sp
    VString        -> False
    VF t           -> go d t
    VThunk t       -> go d t


-- Elimination

($$) :: HasCallStack => Type -> Type -> Type
VNe h ts es $$ a = VNe h ts (es :> a)
_           $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (HasCallStack, Foldable t) => Type -> t Type -> Type
($$*) = foldl' ($$)

infixl 9 $$, $$*

($$$) :: HasCallStack => Type -> Type -> Type
VNe h ts es   $$$ t = VNe h (ts :> t) es
VForAll _ _ b $$$ t = b t
_             $$$ _ = error "can’t apply non-neutral/forall type"

($$$*) :: (HasCallStack, Foldable t) => Type -> t Type -> Type
($$$*) = foldl' ($$)

infixl 9 $$$, $$$*


app :: HasCallStack => Type' C -> Type' V -> Type' C
app (Ne h ts es) a = Ne h ts (es :> a)
app _            _ = error "can’t apply non-neutral/forall type"

inst :: HasCallStack => Type' C -> Type' V -> Type' C
inst (Ne h ts es)   t = Ne h (ts :> t) es
inst (ForAll _ _ b) t = b t
inst _              _ = error "can’t apply non-neutral/forall type"


-- Debugging

showType :: Snoc ShowP -> Type -> ShowP
showType env = \case
  VType         -> string "Type"
  VInterface    -> string "Interface"
  VForAll n t b -> prec 0 $ brace (name n <+> char ':' <+> setPrec 0 (showType env t)) <+> string "->" <+> setPrec 0 (showType (env :> name n) (b (free (Level (length env)))))
  VArrow n q t b  -> case n of
    Just  n -> paren (name n <+> char ':' <+> mult q (showType env t)) <+> string "->" <+> setPrec 0 (showType env b)
    Nothing -> setPrec 1 (mult q (showType env t)) <+> string "->" <+> setPrec 0 (showType env b)
  VNe f ts as   -> head f $$* (brace . showType env <$> ts) $$* (setPrec 11 . showType env <$> as)
  VComp s t     -> sig s <+> showType env t
  VString       -> string "String"
  VF t          -> showType env t
  VThunk t          -> showType env t
  where
  sig s = bracket (commaSep (map (showType env) s))
  ($$*) = foldl' (\ f a -> prec 10 (f <+> a))
  infixl 9 $$*
  head = \case
    Global q  -> qname q
    Free v    -> env ! getIndex (levelToIndex (Level (length env)) v)
    Metavar m -> char '?' <> string (show (getMeta m))
  mult q = if
    | q == zero -> (char '0' <+>)
    | q == one  -> (char '1' <+>)
    | otherwise -> id


-- Type expressions

data TExpr
  = TType
  | TInterface
  | TString
  | TVar (Var Meta Index)
  | TForAll Name TExpr TExpr
  | TArrow (Maybe Name) Quantity TExpr TExpr
  | TComp [TExpr] TExpr
  | TInst TExpr TExpr
  | TApp TExpr TExpr
  | TF TExpr
  | TThunk TExpr
  deriving (Eq, Ord, Show)

data TExpr' u where
  TXForAll :: Name -> TExpr' V -> TExpr' C -> TExpr' C
  TXArrow :: Maybe Name -> Quantity -> TExpr' V -> TExpr' C -> TExpr' C
  TXComp :: [TExpr' V] -> TExpr' V -> TExpr' C
  TXInst :: TExpr' C -> TExpr' V -> TExpr' C
  TXApp :: TExpr' C -> TExpr' V -> TExpr' C
  TXF :: TExpr' V -> TExpr' C
  TXType :: TExpr' V
  TXInterface :: TExpr' V
  TXString :: TExpr' V
  TXVar :: Var Meta Index -> TExpr' V
  TXThunk :: TExpr' C -> TExpr' V

deriving instance Eq   (TExpr' u)
deriving instance Ord  (TExpr' u)
deriving instance Show (TExpr' u)


-- Quotation

quote :: Level -> Type -> TExpr
quote d = \case
  VType          -> TType
  VInterface     -> TInterface
  VString        -> TString
  VForAll n t b  -> TForAll n (quote d t) (quote (succ d) (b (free d)))
  VArrow n q a b -> TArrow n q (quote d a) (quote d b)
  VComp s t      -> TComp (quote d <$> s) (quote d t)
  VNe n ts sp    -> foldl' (&) (foldl' (&) (TVar (levelToIndex d <$> n)) (flip TInst . quote d <$> ts)) (flip TApp . quote d <$> sp)
  VF t           -> TF (quote d t)
  VThunk t       -> TThunk (quote d t)

quote' :: Level -> Type' u -> TExpr' u
quote' d = \case
  ForAll n t b  -> TXForAll n (quote' d t) (quote' (succ d) (b (Var (Free d))))
  Arrow n q a b -> TXArrow n q (quote' d a) (quote' d b)
  Comp s t      -> TXComp (quote' d <$> s) (quote' d t)
  Ne n ts sp    -> foldl' (&) (foldl' (&) (TXF (TXVar (levelToIndex d <$> n))) (flip TXInst . quote' d <$> ts)) (flip TXApp . quote' d <$> sp)
  F t           -> TXF (quote' d t)
  Var n         -> TXVar (levelToIndex d <$> n)
  Type          -> TXType
  Interface     -> TXInterface
  String        -> TXString
  Thunk t       -> TXThunk (quote' d t)

eval :: HasCallStack => Subst Type -> Snoc (Either Type a) -> TExpr -> Type
eval subst = go where
  go env = \case
    TType            -> VType
    TInterface       -> VInterface
    TString          -> VString
    TVar (Global n)  -> global n
    TVar (Free v)    -> fromLeft (error ("term variable at index " <> show v)) (env ! getIndex v)
    TVar (Metavar m) -> maybe (metavar m) tm (lookupMeta m subst)
    TForAll n t b    -> VForAll n (go env t) (\ v -> go (env :> Left v) b)
    TArrow n q a b   -> VArrow n q (go env a) (go env b)
    TComp s t        -> VComp (go env <$> s) (go env t)
    TInst f a        -> go env f $$$ go env a
    TApp  f a        -> go env f $$  go env a
    TF t             -> VF (go env t)
    TThunk t         -> VThunk (go env t)

eval' :: HasCallStack => Subst (Type' V) -> Snoc (Either (Type' V) a) -> TExpr' u -> Type' u
eval' subst = go where
  go :: Snoc (Either (Type' V) a) -> TExpr' u -> Type' u
  go env = \case
    TXForAll n t b    -> ForAll n (go env t) (\ v -> go (env :> Left v) b)
    TXArrow n q a b   -> Arrow n q (go env a) (go env b)
    TXComp s t        -> Comp (go env <$> s) (go env t)
    TXInst f a        -> go env f `inst` go env a
    TXApp  f a        -> go env f `app`  go env a
    TXF t             -> F (go env t)
    TXType            -> Type
    TXInterface       -> Interface
    TXString          -> String
    TXVar (Global n)  -> Var (Global n)
    TXVar (Free v)    -> fromLeft (error ("term variable at index " <> show v)) (env ! getIndex v)
    TXVar (Metavar m) -> maybe (Var (Metavar m)) tm (lookupMeta m subst)
    TXThunk t         -> Thunk (go env t)


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
