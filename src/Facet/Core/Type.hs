module Facet.Core.Type
( -- * Types
  Interface(..)
, Type(..)
, global
, free
, metavar
, unComp
, unThunk
, occursIn
  -- * Type expressions
, TExpr(..)
  -- * Shifts
, Shift(..)
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
import           Data.Maybe (fromMaybe)
import           Facet.Name
import           Facet.Snoc
import           Facet.Syntax
import           Facet.Usage
import           GHC.Stack
import           Prelude hiding (lookup)

-- Types

newtype Interface ty = IInterface { getInterface :: ty }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)


data Type
  -- Types
  = Type
  | Interface

  -- Negative
  | ForAll Name Type (Type -> Type)
  | Arrow (Maybe Name) Quantity Type Type
  | Comp [Interface Type] Type

  -- Positive
  | Ne (Var Meta Level) (Snoc Type)
  | String
  | Thunk Type

instance Shift Type where
  shiftP t = fromMaybe (Comp [] t) (unThunk t)
  shiftN = \case
    Comp [] t -> t
    t         -> Thunk t

global :: QName -> Type
global n = Ne (Global n) Nil

free :: Level -> Type
free l = Ne (Free l) Nil

metavar :: Meta -> Type
metavar m = Ne (Metavar m) Nil


-- | The polarity of a 'Type'. Returns in 'Maybe' because some 'Type's (e.g. 'Type' itself) are kinds, which aren’t polarized.
instance HasPolarity Type where
  polarity = \case
    Type          -> Nothing
    Interface     -> Nothing
    -- FIXME: it would be nice for this to be more nuanced, e.g. the @nil@ list constructor of type @{ A : Type } -> List A@ could reasonably be positive since the forall doesn’t do computation
    ForAll{}      -> Just Neg
    -- the body is either a kind (@'Nothing'@) or negative (@'Just' 'Neg'@), so we just use its polarity for the arrow as a whole
    Arrow _ _ _ b -> polarity b
    Comp{}        -> Just Neg
    -- FIXME: this will need to be reconsidered if we ever allow type constructors with arbitrary polarities, or e.g. embed the kind arrow as a symbol
    -- FIXME: List is neutral (being as it’s Type -> Type), List A is positive, and there’s no guarantee that the neutral term is saturated
    Ne{}          -> Just Pos
    String        -> Just Pos
    Thunk{}       -> Just Pos


unComp :: Has Empty sig m => Type -> m ([Interface Type], Type)
unComp = \case
  Comp sig _T -> pure (sig, _T)
  _T          -> empty

unThunk :: Has Empty sig m => Type -> m Type
unThunk = \case
  Thunk t -> pure t
  _       -> empty


occursIn :: (Var Meta Level -> Bool) -> Level -> Type -> Bool
occursIn p = go
  where
  go :: Level -> Type -> Bool
  go d = \case
    Type          -> False
    Interface     -> False
    ForAll  _ t b -> go d t || go (succ d) (b (free d))
    Arrow _ _ a b -> go d a || go d b
    Comp s t      -> any (go d . getInterface) s || go d t
    Ne h sp       -> p h || any (go d) sp
    String        -> False
    Thunk t       -> go d t


-- Elimination

app :: HasCallStack => Type -> Type -> Type
app (Ne h es) a = Ne h (es :> a)
app _         _ = error "can’t apply non-neutral/forall type"


-- Type expressions

data TExpr
  = TType
  | TInterface

  | TForAll Name TExpr TExpr
  | TArrow (Maybe Name) Quantity TExpr TExpr
  | TComp [Interface TExpr] TExpr

  | TVar (Var Meta Index)
  | TApp TExpr TExpr
  | TString
  | TThunk TExpr
  deriving (Eq, Ord, Show)

instance Shift TExpr where
  shiftP = \case
    TThunk t -> t
    t        -> TComp [] t
  shiftN = \case
    TComp [] t -> t
    t          -> TThunk t


-- Shifting

class Shift t where
  shiftP :: t -> t
  shiftN :: t -> t


-- Quotation

quote :: Level -> Type -> TExpr
quote d = \case
  Type          -> TType
  Interface     -> TInterface

  ForAll n t b  -> TForAll n (quote d t) (quote (succ d) (b (free d)))
  Arrow n q a b -> TArrow n q (quote d a) (quote d b)
  Comp s t      -> TComp (IInterface . quote d . getInterface <$> s) (quote d t)

  Ne n sp       -> foldl' TApp (TVar (levelToIndex d <$> n)) (quote d <$> sp)
  String        -> TString
  Thunk t       -> TThunk (quote d t)

eval :: HasCallStack => Subst -> Snoc (Either Type a) -> TExpr -> Type
eval subst = go where
  go :: Snoc (Either Type a) -> TExpr -> Type
  go env = \case
    TType            -> Type
    TInterface       -> Interface
    TForAll n t b    -> ForAll n (go env t) (\ v -> go (env :> Left v) b)
    TArrow n q a b   -> Arrow n q (go env a) (go env b)
    TComp s t        -> Comp (IInterface . go env . getInterface <$> s) (go env t)
    TApp f a         -> go env f `app` go env a
    TString          -> String
    TVar (Global n)  -> global n
    TVar (Free v)    -> fromLeft (error ("term variable at index " <> show v)) (env ! getIndex v)
    TVar (Metavar m) -> maybe (metavar m) tm (lookupMeta m subst)
    TThunk t         -> Thunk (go env t)


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
