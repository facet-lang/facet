module Facet.Type.Norm
( -- * Types
  Type(..)
, global
, free
, metavar
, unNeutral
, unComp
, Classifier(..)
, classifierType
, occursIn
  -- ** Elimination
, ($$)
, ($$*)
  -- * Quotation
, quote
, eval
, apply
) where

import Control.Effect.Empty
import Data.Foldable (foldl')
import Data.Function (on, (&))
import Data.Maybe (fromMaybe)
import Facet.Env hiding (empty)
import Facet.Interface
import Facet.Kind
import Facet.Name
import Facet.Pattern
import Facet.Snoc
import Facet.Subst
import Facet.Syntax
import Facet.Type.Expr
import Facet.Usage hiding (singleton)
import GHC.Stack
import Prelude hiding (lookup)

-- Types

data Type
  = VString
  | VForAll Name Kind (Type -> Type)
  | VArrow (Maybe Name) Quantity Type Type
  | VNe (Var (Either Meta (LName Level))) (Snoc Type)
  | VComp (Signature Type) Type

instance Eq Type where
  (==) = (==) `on` quote 0

instance Ord Type where
  compare = compare `on` quote 0


global :: RName -> Type
global = var . Global

free :: LName Level -> Type
free = var . Free . Right

metavar :: Meta -> Type
metavar = var . Free . Left


var :: Var (Either Meta (LName Level)) -> Type
var v = VNe v Nil


unNeutral :: Has Empty sig m => Type -> m (Var (Either Meta (LName Level)), Snoc Type)
unNeutral = \case
  VNe h sp -> pure (h, sp)
  _        -> empty

unComp :: Has Empty sig m => Type -> m (Signature Type, Type)
unComp = \case
  VComp sig _T -> pure (sig, _T)
  _T           -> empty


data Classifier
  = CK Kind
  | CT Type

classifierType :: Classifier -> Maybe Type
classifierType = \case
  CK _K -> empty
  CT _T -> pure _T


occursIn :: Meta -> Level -> Type -> Bool
occursIn p = go
  where
  go d = \case
    VForAll n _ b  -> go (succ d) (b (free (LName d n)))
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


-- Quotation

quote :: Level -> Type -> TExpr
quote d = \case
  VString        -> TString
  VForAll n t b  -> TForAll n t (quote (succ d) (b (free (LName d n))))
  VArrow n q a b -> TArrow n q (quote d a) (quote d b)
  VComp s t      -> TComp (mapSignature (quote d) s) (quote d t)
  VNe n sp       -> foldl' (&) (TVar (fmap (fmap (levelToIndex d)) <$> n)) (flip TApp . quote d <$> sp)

eval :: HasCallStack => Subst Type -> Env Type -> TExpr -> Type
eval subst = go where
  go env = \case
    TString               -> VString
    TVar (Global n)       -> global n
    TVar (Free (Right n)) -> index env n
    TVar (Free (Left m))  -> fromMaybe (metavar m) (lookupMeta m subst)
    TForAll n t b         -> VForAll n t (\ _T -> go (env |> PVar (n :=: _T)) b)
    TArrow n q a b        -> VArrow n q (go env a) (go env b)
    TComp s t             -> VComp (mapSignature (go env) s) (go env t)
    TApp  f a             -> go env f $$  go env a

apply :: HasCallStack => Subst Type -> Env Type -> Type -> Type
apply subst env = eval subst env . quote (level env)
