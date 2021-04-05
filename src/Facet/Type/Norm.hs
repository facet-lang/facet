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
  = String
  | ForAll Name Kind (Type -> Type)
  | Arrow (Maybe Name) Quantity Type Type
  | Ne (Var (Either Meta (LName Level))) (Snoc Type)
  | Comp (Signature Type) Type

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
var v = Ne v Nil


unNeutral :: Has Empty sig m => Type -> m (Var (Either Meta (LName Level)), Snoc Type)
unNeutral = \case
  Ne h sp -> pure (h, sp)
  _       -> empty

unComp :: Has Empty sig m => Type -> m (Signature Type, Type)
unComp = \case
  Comp sig _T -> pure (sig, _T)
  _T          -> empty


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
    ForAll n _ b  -> go (succ d) (b (free (LName d n)))
    Arrow _ _ a b -> go d a || go d b
    Comp s t      -> any (go d) s || go d t
    Ne h sp       -> any (either (== p) (const False)) h || any (go d) sp
    String        -> False


-- Elimination

($$) :: HasCallStack => Type -> Type -> Type
Ne h es $$ a = Ne h (es :> a)
_       $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (HasCallStack, Foldable t) => Type -> t Type -> Type
($$*) = foldl' ($$)

infixl 9 $$, $$*


-- Quotation

quote :: Level -> Type -> TExpr
quote d = \case
  String        -> TString
  ForAll n t b  -> TForAll n t (quote (succ d) (b (free (LName d n))))
  Arrow n q a b -> TArrow n q (quote d a) (quote d b)
  Comp s t      -> TComp (mapSignature (quote d) s) (quote d t)
  Ne n sp       -> foldl' (&) (TVar (fmap (fmap (levelToIndex d)) <$> n)) (flip TApp . quote d <$> sp)

eval :: HasCallStack => Subst Type -> Env Type -> TExpr -> Type
eval subst = go where
  go env = \case
    TString               -> String
    TVar (Global n)       -> global n
    TVar (Free (Right n)) -> index env n
    TVar (Free (Left m))  -> fromMaybe (metavar m) (lookupMeta m subst)
    TForAll n t b         -> ForAll n t (\ _T -> go (env |> PVar (n :=: _T)) b)
    TArrow n q a b        -> Arrow n q (go env a) (go env b)
    TComp s t             -> Comp (mapSignature (go env) s) (go env t)
    TApp  f a             -> go env f $$  go env a

apply :: HasCallStack => Subst Type -> Env Type -> Type -> Type
apply subst env = eval subst env . quote (level env)
