module Facet.Type.Norm
( -- * Types
  Type(..)
, _String
, _ForAll
, _Arrow
, _Ne
, _Comp
  -- ** Construction
, bound
, free
, metavar
, (-->)
, unNeutral
, unComp
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
import           Data.List (intersperse)
import           Data.Maybe (fromMaybe)
import           Facet.Interface
import           Facet.Kind
import           Facet.Name
import           Facet.Pretty (toAlpha)
import           Facet.Quote
import           Facet.Snoc
import           Facet.Subst
import           Facet.Syntax
import qualified Facet.Type.Class as C
import qualified Facet.Type.Expr as TX
import           Fresnel.Getter ((^.))
import           Fresnel.Prism (Prism', prism')
import           GHC.Stack
import           Prelude hiding (lookup)

-- Types

data Type
  = String
  | ForAll Name Kind (Type -> Type)
  | Arrow (Maybe Name) Type Type
  | Ne (Var (Either Meta Level)) (Snoc Type)
  | Comp (Signature Type) Type
  deriving (Eq, Ord) via Quoting TX.Type Type

instance C.Type Type where
  string = String
  forAll = ForAll
  arrow = Arrow
  var = Facet.Type.Norm.var
  ($$) = (Facet.Type.Norm.$$)
  h $$$ sp = Ne h (foldl' (:>) Nil sp)
  (|-) = Comp

instance Quote Type TX.Type where
  quote = \case
    String       -> pure TX.String
    ForAll n t b -> Quoter (\ d -> TX.ForAll n t (runQuoter (succ d) (quote (b (bound d)))))
    Arrow n a b  -> TX.Arrow n <$> quote a <*> quote b
    Comp s t     -> TX.Comp <$> traverseSignature quote s <*> quote t
    Ne n sp      -> foldl' (\ h t -> TX.App <$> h <*> quote t) (Quoter (\ d -> TX.Var (toIndexed d n))) sp

instance Show Type where
  showsPrec = go 0
    where
    go d p = \case
      String            -> showString "String"
      ForAll n k b      -> showParen (p > 10) $ showString "ForAll " . showsPrec 11 n . showChar ' ' . showsPrec 11 k . showChar ' ' . showParen True (showString "\\ " . showsLevel d . showString " -> ". go (succ d) 0 (b (bound d)))
      Arrow Nothing a b -> showParen (p > 1) $ go d 2 a . showString " --> " . go d 1 b
      Arrow n a b       -> showParen (p > 10) $ showString "Arrow " . showsPrec 11 n . showChar ' ' . go d 11 a . showChar ' ' . go d 11 b
      Ne v ts           -> showParen (p > 10) $ showString "Ne " . showsVar v . showString " [" . showsFoldable (go d 0) ts . showChar ']'
      Comp s t          -> showParen (p > 10) $ showString "Comp [" . showsFoldable (go d 0) s . showString "] " . go d 11 t
    showsVar = \case
      Bound (Left (Meta v)) -> showChar 'σ' . shows v
      Bound (Right d)       -> showsLevel d
      Free n                -> shows n
    showsLevel (Level v) = showString (toAlpha ['a'..'z'] v)
    showsFoldable f s = foldr (.) id (intersperse (showString ", ") (foldr ((:) . f) [] s))

_String :: Prism' Type ()
_String = prism' (const String) (\case{ String -> Just () ; _ -> Nothing })

_ForAll :: Prism' Type (Name, Kind, Type -> Type)
_ForAll = prism' (\ (n, k, b) -> ForAll n k b) (\case{ ForAll n k b -> Just (n, k, b) ; _ -> Nothing })

_Arrow :: Prism' Type (Maybe Name, Type, Type)
_Arrow = prism' (\ (n, a, b) -> Arrow n a b) (\case{ Arrow n a b -> Just (n, a, b) ; _ -> Nothing })

_Ne :: Prism' Type (Var (Either Meta Level), Snoc Type)
_Ne = prism' (uncurry Ne) (\case{ Ne c ts -> Just (c, ts) ; _ -> Nothing })

_Comp :: Prism' Type (Signature Type, Type)
_Comp = prism' (uncurry Comp) (\case{ Comp sig t -> Just (sig, t) ; _ -> Nothing })


bound :: Level -> Type
bound = var . Bound . Right

free :: QName -> Type
free = var . Free

metavar :: Meta -> Type
metavar = var . Bound . Left


var :: Var (Either Meta Level) -> Type
var v = Ne v Nil


(-->) :: Type -> Type -> Type
(-->) = Arrow Nothing

infixr 1 -->


unNeutral :: Has Empty sig m => Type -> m (Var (Either Meta Level), Snoc Type)
unNeutral = \case
  Ne h sp -> pure (h, sp)
  _       -> empty

unComp :: Has Empty sig m => Type -> m (Signature Type, Type)
unComp = \case
  Comp sig _T -> pure (sig, _T)
  _T          -> empty


occursIn :: Meta -> Level -> Type -> Bool
occursIn p = go
  where
  go d = \case
    ForAll _ _ b -> go (succ d) (b (bound d))
    Arrow _ a b  -> go d a || go d b
    Comp s t     -> any (go d) s || go d t
    Ne h sp      -> any (either (== p) (const False)) h || any (go d) sp
    String       -> False


-- Elimination

($$) :: HasCallStack => Type -> Type -> Type
Ne h es $$ a = Ne h (es :> a)
_       $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (HasCallStack, Foldable t) => Type -> t Type -> Type
($$*) = foldl' ($$)

infixl 9 $$, $$*


-- Quotation

eval :: HasCallStack => Subst Type -> Snoc (Name :=: Type) -> TX.Type -> Type
eval subst = go where
  go env = \case
    TX.String                -> String
    TX.Var (Free n)          -> free n
    TX.Var (Bound (Right n)) -> (env ! getIndex n) ^. def_
    TX.Var (Bound (Left m))  -> fromMaybe (metavar m) (lookupMeta m subst)
    TX.ForAll n t b          -> ForAll n t (\ _T -> go (env :> (n :=: _T)) b)
    TX.Arrow n a b           -> Arrow n (go env a) (go env b)
    TX.Comp s t              -> Comp (mapSignature (go env) s) (go env t)
    TX.App  f a              -> go env f $$ go env a

apply :: HasCallStack => Subst Type -> Snoc (Name :=: Type) -> Type -> Type
apply subst env = eval subst env . runQuoter (Level (length env)) . quote
