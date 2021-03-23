module Facet.Core.Type
( -- * Kinds
  Kind(..)
  -- * Types
, Interface(..)
, NType(..)
, PType(..)
, pglobal
, pfree
, pmetavar
, Type(..)
, global
, free
, metavar
, unComp
, Subject(..)
, subjectType
, occursInN
, occursInP
, occursIn
  -- ** Elimination
, ($$)
, ($$*)
  -- * Type expressions
, NTExpr(..)
, PTExpr(..)
, TExpr(..)
  -- * Quotation
, quoteN
, quoteP
, quote
, evalN
, evalP
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

data NType
  = NComp [Interface PType] PType
  | NArrow (Maybe Name) Quantity PType NType
  | NForAll Name Kind (PType -> NType)

data PType
  = PString
  | PNe (Var (Either Meta Level)) (Snoc PType)
  | PThunk NType


pglobal :: RName -> PType
pglobal = pvar . Global

pfree :: Level -> PType
pfree = pvar . Free . Right

pmetavar :: Meta -> PType
pmetavar = pvar . Free . Left


pvar :: Var (Either Meta Level) -> PType
pvar v = PNe v Nil


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
  | SN NType
  | SP PType
  | ST Type

subjectType :: Subject -> Maybe Type
subjectType = \case
  SK _K -> empty
  SN _N -> empty
  SP _P -> empty
  ST _T -> pure _T


occursInN :: (Var (Either Meta Level) -> Bool) -> Level -> NType -> Bool
occursInN p = go
  where
  go d = \case
    NForAll _ _ b  -> go (succ d) (b (pfree d))
    NArrow _ _ a b -> occursInP p d a || go d b
    NComp s t      -> any (goI d) s || occursInP p d t
  goI d (Interface h sp) = p (Global h) || any (occursInP p d) sp

occursInP :: (Var (Either Meta Level) -> Bool) -> Level -> PType -> Bool
occursInP p = go
  where
  go d = \case
    PNe h sp -> p h || any (go d) sp
    PThunk n -> occursInN p d n
    PString  -> False

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

papp :: HasCallStack => PType -> PType -> PType
PNe h es `papp` a = PNe h (es :> a)
_        `papp` _ = error "can’t apply non-neutral/forall type"

($$) :: HasCallStack => Type -> Type -> Type
VNe h es $$ a = VNe h (es :> a)
_        $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (HasCallStack, Foldable t) => Type -> t Type -> Type
($$*) = foldl' ($$)

infixl 9 $$, $$*


-- Type expressions

data NTExpr
  = NTXForAll Name Kind NTExpr
  | NTXArrow (Maybe Name) Quantity PTExpr NTExpr
  | NTXComp [Interface PTExpr] PTExpr
  deriving (Eq, Ord, Show)

data PTExpr
  = PTXString
  | PTXVar (Var (Either Meta Index))
  | PTXThunk NTExpr
  | PTXApp PTExpr PTExpr
  deriving (Eq, Ord, Show)

data TExpr
  = TString
  | TVar (Var (Either Meta Index))
  | TForAll Name Kind TExpr
  | TArrow (Maybe Name) Quantity TExpr TExpr
  | TComp [Interface TExpr] TExpr
  | TApp TExpr TExpr
  deriving (Eq, Ord, Show)


-- Quotation

quoteN :: Level -> NType -> NTExpr
quoteN d = \case
  NForAll n   t b -> NTXForAll n t (quoteN (succ d) (b (pfree d)))
  NArrow  n q a b -> NTXArrow n q (quoteP d a) (quoteN d b)
  NComp       s p -> NTXComp (fmap (quoteP d) <$> s) (quoteP d p)

quoteP :: Level -> PType -> PTExpr
quoteP d = \case
  PString  -> PTXString
  PNe n sp -> foldl' (&) (PTXVar (fmap (levelToIndex d) <$> n)) (flip PTXApp . quoteP d <$> sp)
  PThunk n -> PTXThunk (quoteN d n)

quote :: Level -> Type -> TExpr
quote d = \case
  VString        -> TString
  VForAll n t b  -> TForAll n t (quote (succ d) (b (free d)))
  VArrow n q a b -> TArrow n q (quote d a) (quote d b)
  VComp s t      -> TComp (fmap (quote d) <$> s) (quote d t)
  VNe n sp       -> foldl' (&) (TVar (fmap (levelToIndex d) <$> n)) (flip TApp . quote d <$> sp)

eval :: HasCallStack => Subst Type -> Snoc (Either Type a) -> TExpr -> Type
eval subst = go where
  go env = \case
    TString               -> VString
    TVar (Global n)       -> global n
    TVar (Free (Right v)) -> fromLeft (error ("term variable at index " <> show v)) (env ! getIndex v)
    TVar (Free (Left m))  -> maybe (metavar m) tm (lookupMeta m subst)
    TForAll n t b         -> VForAll n t (\ v -> go (env :> Left v) b)
    TArrow n q a b        -> VArrow n q (go env a) (go env b)
    TComp s t             -> VComp (fmap (go env) <$> s) (go env t)
    TApp  f a             -> go env f $$  go env a

evalN :: HasCallStack => Subst PType -> Snoc (Either PType a) -> NTExpr -> NType
evalN subst env = \case
  NTXForAll n   t b -> NForAll n t (\ v -> evalN subst (env :> Left v) b)
  NTXArrow  n q a b -> NArrow n q (evalP subst env a) (evalN subst env b)
  NTXComp       s p -> NComp (fmap (evalP subst env) <$> s) (evalP subst env p)

evalP :: HasCallStack => Subst PType -> Snoc (Either PType a) -> PTExpr -> PType
evalP subst env = \case
  PTXString               -> PString
  PTXVar (Global n)       -> pglobal n
  PTXVar (Free (Right v)) -> fromLeft (error ("term variable at index " <> show v)) (env ! getIndex v)
  PTXVar (Free (Left m))  -> maybe (pmetavar m) tm (lookupMeta m subst)
  PTXThunk n              -> PThunk (evalN subst env n)
  PTXApp f a              -> evalP subst env f `papp` evalP subst env a


-- Substitution

newtype Subst t = Subst (IntMap.IntMap (Maybe t ::: Kind))
  deriving (Monoid, Semigroup)

insert :: Meta -> Maybe t ::: Kind -> Subst t -> Subst t
insert (Meta i) t (Subst metas) = Subst (IntMap.insert i t metas)

lookupMeta :: Meta -> Subst t -> Maybe (t ::: Kind)
lookupMeta (Meta i) (Subst metas) = do
  v ::: _T <- IntMap.lookup i metas
  (::: _T) <$> v

solveMeta :: Meta -> t -> Subst t -> Subst t
solveMeta (Meta i) t (Subst metas) = Subst (IntMap.update (\ (_ ::: _T) -> Just (Just t ::: _T)) i metas)

declareMeta :: Kind -> Subst t -> (Subst t, Meta)
declareMeta _K (Subst metas) = (Subst (IntMap.insert v (Nothing ::: _K) metas), Meta v) where
  v = maybe 0 (succ . fst . fst) (IntMap.maxViewWithKey metas)

metas :: Subst t -> [Meta :=: Maybe t ::: Kind]
metas (Subst metas) = map (\ (k, v) -> Meta k :=: v) (IntMap.toList metas)
