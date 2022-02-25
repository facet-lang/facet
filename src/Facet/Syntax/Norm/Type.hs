module Facet.Syntax.Norm.Type
( -- * Types
  Type(..)
, _String
, _ForAll
, _Arrow
, _Ne
, _Comp
, global
, free
, metavar
, unNeutral
, unComp
, Classifier(..)
, Classified(..)
, occursIn
  -- ** Elimination
, ($$)
, ($$*)
  -- * Evaluation
, eval
, apply
) where

import           Control.Effect.Empty
import           Data.Foldable (foldl')
import           Data.Maybe (fromMaybe)
import           Facet.Env hiding (empty)
import           Facet.Interface
import           Facet.Kind
import           Facet.Name
import           Facet.Quote
import           Facet.Snoc
import           Facet.Subst
import           Facet.Syntax
import qualified Facet.Syntax.Expr.Type as TX
import           Facet.Syntax.Pattern
import qualified Facet.Type.Class as C
import           Facet.Usage hiding (singleton)
import           Fresnel.Prism (Prism', prism')
import           GHC.Stack
import           Prelude hiding (lookup)

-- Types

data Type
  = String
  | ForAll Name Kind (Type -> Type)
  | Arrow (Maybe Name) Quantity Type Type
  | Ne (Var (Either Meta (LName Level))) (Snoc Type)
  | Comp (Signature Type) Type
  deriving (Eq, Ord, Show) via Quoting TX.Type Type

instance C.Type Type where
  string = String
  forAll = ForAll
  arrow = Arrow
  var = Facet.Syntax.Norm.Type.var
  ($$) = (Facet.Syntax.Norm.Type.$$)
  (|-) = Comp

instance Quote Type TX.Type where
  quote = \case
    String        -> pure TX.String
    ForAll n t b  -> Quoter (\ d -> TX.ForAll n t (runQuoter (succ d) (quote (b (free (LName (getUsed d) n))))))
    Arrow n q a b -> TX.Arrow n q <$> quote a <*> quote b
    Comp s t      -> TX.Comp <$> traverseSignature quote s <*> quote t
    Ne n sp       -> foldl' (\ h t -> TX.App <$> h <*> quote t) (Quoter (\ d -> TX.Var (toIndexed d n))) sp


_String :: Prism' Type ()
_String = prism' (const String) (\case{ String -> Just () ; _ -> Nothing })

_ForAll :: Prism' Type (Name, Kind, Type -> Type)
_ForAll = prism' (\ (n, k, b) -> ForAll n k b) (\case{ ForAll n k b -> Just (n, k, b) ; _ -> Nothing })

_Arrow :: Prism' Type (Maybe Name, Quantity, Type, Type)
_Arrow = prism' (\ (n, q, a, b) -> Arrow n q a b) (\case{ Arrow n q a b -> Just (n, q, a, b) ; _ -> Nothing })

_Ne :: Prism' Type (Var (Either Meta (LName Level)), Snoc Type)
_Ne = prism' (uncurry Ne) (\case{ Ne c ts -> Just (c, ts) ; _ -> Nothing })

_Comp :: Prism' Type (Signature Type, Type)
_Comp = prism' (uncurry Comp) (\case{ Comp sig t -> Just (sig, t) ; _ -> Nothing })


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

class Classified t where
  classified :: t -> Classifier

instance Classified Kind where
  classified = CK

instance Classified Type where
  classified = CT


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

eval :: HasCallStack => Subst Type -> Env Type -> TX.Type -> Type
eval subst = go where
  go env = \case
    TX.String               -> String
    TX.Var (Global n)       -> global n
    TX.Var (Free (Right n)) -> index env n
    TX.Var (Free (Left m))  -> fromMaybe (metavar m) (lookupMeta m subst)
    TX.ForAll n t b         -> ForAll n t (\ _T -> go (env |> PVar (n :=: _T)) b)
    TX.Arrow n q a b        -> Arrow n q (go env a) (go env b)
    TX.Comp s t             -> Comp (mapSignature (go env) s) (go env t)
    TX.App  f a             -> go env f $$  go env a

apply :: HasCallStack => Subst Type -> Env Type -> Type -> Type
apply subst env = eval subst env . runQuoter (level env) . quote
