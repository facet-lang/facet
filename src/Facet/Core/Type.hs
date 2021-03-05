module Facet.Core.Type
( -- * Types
  Sorted(..)
, unSTerm
, unSType
, Interface(..)
, Kind(..)
, kglobal
, kapp
, NType
, PType
, Type(..)
, global
, free
, metavar
, unComp
, unThunk
, occursIn
  -- * Type expressions
, NTExpr
, PTExpr
, TExpr(..)
  -- ** Negative type constructors
, Neg
, forAllT
, arrowT
, compT
  -- ** Positive type constructors
, Pos
, varT
, appT
, stringT
, thunkT
  -- ** Type eliminators
, unarrowT
, uncompT
, unthunkT
  -- * Quotation
, quote
, eval
) where

import Control.Effect.Empty
import Data.Either (fromLeft)
import Data.Foldable (foldl')
import Facet.Name
import Facet.Snoc
import Facet.Subst
import Facet.Syntax
import Facet.Usage
import GHC.Stack
import Prelude hiding (lookup)

-- Types

data Sorted
  = STerm Type
  | SType Kind

unSTerm :: Has Empty sig m => Sorted -> m Type
unSTerm = \case{ STerm ty -> pure ty ; _ -> empty }

unSType :: Has Empty sig m => Sorted -> m Kind
unSType = \case{ SType ki -> pure ki ; _ -> empty }


newtype Interface = IInterface { getInterface :: Kind }
  deriving (Eq, Ord, Show)

data Kind
  = Type
  | Interface
  | KArrow (Maybe Name) Kind Kind
  | KSpine QName (Snoc Kind)
  deriving (Eq, Ord, Show)

kglobal :: QName -> Kind
kglobal n = KSpine n Nil

kapp :: Kind -> Kind -> Kind
kapp (KSpine h as) a = KSpine h (as :> a)
kapp _             _ = error "invalid kind application"


type NType = Type
type PType = Type

data Type
  -- Negative
  = ForAll Name Kind (PType -> NType)
  | Arrow (Maybe Name) Quantity PType NType
  | Comp [Interface] PType

  -- Positive
  | Ne (Var Meta Level) (Snoc PType)
  | String
  | Thunk NType


global :: QName -> Type
global n = Ne (Global n) Nil

free :: Level -> Type
free l = Ne (Free l) Nil

metavar :: Meta -> Type
metavar m = Ne (Metavar m) Nil


unComp :: Has Empty sig m => Type -> m ([Interface], Type)
unComp = \case
  Comp sig _T -> pure (sig, _T)
  _T          -> empty

unThunk :: Has Empty sig m => Type -> m Type
unThunk = \case
  Thunk t -> pure t
  _       -> empty


occursIn :: Meta -> Level -> Type -> Bool
occursIn v = go
  where
  go :: Level -> Type -> Bool
  go d = \case
    ForAll  _ _ b -> go (succ d) (b (free d))
    Arrow _ _ a b -> go d a || go d b
    Comp _ t      -> go d t
    Ne h sp       -> Metavar v == h || any (go d) sp
    String        -> False
    Thunk t       -> go d t



-- Elimination

app :: HasCallStack => Type -> Type -> Type
app (Ne h es) a = Ne h (es :> a)
app _         _ = error "can’t apply non-neutral/forall type"


-- Type expressions

type NTExpr = Neg TExpr
type PTExpr = Pos TExpr

data TExpr
  = TForAll Name Kind TExpr
  | TArrow (Maybe Name) Quantity TExpr TExpr
  | TComp [Interface] TExpr

  | TVar (Var Meta Index)
  | TApp TExpr TExpr
  | TString
  | TThunk TExpr
  deriving (Eq, Ord, Show)


-- Negative type constructors

forAllT :: Name -> Kind -> Neg TExpr -> Neg TExpr
forAllT n t (Neg b) = Neg (TForAll n t b)

arrowT :: Maybe Name -> Quantity -> Pos TExpr -> Neg TExpr -> Neg TExpr
arrowT n q (Pos a) (Neg b) = Neg (TArrow n q a b)

compT :: [Interface] -> Pos TExpr -> Neg TExpr
compT sig (Pos t) = Neg (TComp sig t)


-- Positive type constructors

varT :: Var Meta Index -> Pos TExpr
varT v = Pos (TVar v)

appT :: Pos TExpr -> Pos TExpr -> Pos TExpr
appT (Pos f) (Pos a) = Pos (TApp f a)

stringT :: Pos TExpr
stringT = Pos TString

thunkT :: Neg TExpr -> Pos TExpr
thunkT (Neg t) = Pos (TThunk t)


-- Type eliminators

unarrowT :: Has Empty sig m => Neg TExpr -> m (Maybe Name, Quantity, Pos TExpr, Neg TExpr)
unarrowT = \case
  Neg (TArrow n q a b) -> pure (n, q, Pos a, Neg b)
  _                    -> empty

uncompT :: Has Empty sig m => Neg TExpr -> m ([Interface], Pos TExpr)
uncompT = \case
  Neg (TComp sig _T) -> pure (sig, Pos _T)
  _                  -> empty

unthunkT :: Has Empty sig m => Pos TExpr -> m (Neg TExpr)
unthunkT = \case
  Pos (TThunk _T) -> pure (Neg _T)
  _               -> empty


-- Quotation

quote :: Level -> Type -> TExpr
quote d = \case
  ForAll n t b  -> TForAll n t (quote (succ d) (b (free d)))
  Arrow n q a b -> TArrow n q (quote d a) (quote d b)
  Comp s t      -> TComp s (quote d t)

  Ne n sp       -> foldl' TApp (TVar (levelToIndex d <$> n)) (quote d <$> sp)
  String        -> TString
  Thunk t       -> TThunk (quote d t)

eval :: HasCallStack => Subst Type Kind -> Snoc (Either Type a) -> TExpr -> Type
eval subst = go where
  go :: Snoc (Either Type a) -> TExpr -> Type
  go env = \case
    TForAll n t b    -> ForAll n t (\ v -> go (env :> Left v) b)
    TArrow n q a b   -> Arrow n q (go env a) (go env b)
    TComp s t        -> Comp s (go env t)
    TApp f a         -> go env f `app` go env a
    TString          -> String
    TVar (Global n)  -> global n
    TVar (Free v)    -> fromLeft (error ("term variable at index " <> show v)) (env ! getIndex v)
    TVar (Metavar m) -> maybe (metavar m) tm (lookupMeta m subst)
    TThunk t         -> Thunk (go env t)
