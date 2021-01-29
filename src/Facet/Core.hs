module Facet.Core
( -- * Types
  Type(..)
, TElim(..)
  -- ** Variables
, Var(..)
, unVar
, global
, free
, metavar
, occursIn
  -- ** Elimination
, ($$)
, ($$*)
  -- * Patterns
, ValuePattern(..)
, Pattern(..)
, pvar
, pcon
, fill
, bindPattern
  -- * Modules
, Module(..)
, name_
, imports_
, scope_
, lookupC
, lookupE
, lookupD
, Scope(..)
, decls_
, scopeFromList
, scopeToList
, lookupScope
, Import(..)
, Def(..)
, unDData
, unDInterface
  -- * Expressions
, TExpr(..)
, Expr(..)
  -- * Quotation
, quote
, eval
) where

import           Control.Applicative (Alternative(..))
import           Control.Lens (Lens', coerced, lens)
import           Data.Foldable (asum, foldl')
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.Text (Text)
import           Data.Traversable (mapAccumL)
import           Facet.Name
import           Facet.Stack
import           Facet.Syntax
import           GHC.Stack
import           Prelude hiding (zip, zipWith)

-- Types

data Type
  = VKType
  | VKInterface
  | VTForAll Name Type (Type -> Type)
  | VTArrow (Either Name [Type]) Type Type
  | VTNe (Var Level :$ TElim)
  | VTComp [Type] Type
  | VTString

data TElim
  = TEInst Type
  | TEApp Type


-- Variables

data Var a
  = Global (Q Name) -- ^ Global variables, considered equal by 'QName'.
  | Free a
  | Metavar Meta
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

unVar :: (Q Name -> b) -> (a -> b) -> (Meta -> b) -> Var a -> b
unVar f g h = \case
  Global  n -> f n
  Free    n -> g n
  Metavar n -> h n


global :: Q Name -> Type
global = var . Global

free :: Level -> Type
free = var . Free

metavar :: Meta -> Type
metavar = var . Metavar


var :: Var Level -> Type
var = VTNe . (:$ Nil)


occursIn :: (Var Level -> Bool) -> Level -> Type -> Bool
occursIn p = go
  where
  go d = \case
    VKType         -> False
    VKInterface    -> False
    VTForAll _ t b -> go d t || go (succ d) (b (free d))
    VTArrow n a b  -> any (any (go d)) n || go d a || go d b
    VTComp s t     -> any (go d) s || go d t
    VTNe (h :$ sp) -> p h || any (elim d) sp
    VTString       -> False

  elim d = \case
    TEInst t -> go d t
    TEApp  t -> go d t


-- Elimination

($$) :: HasCallStack => Type -> TElim -> Type
VTNe (h :$ es) $$ a = VTNe (h :$ (es :> a))
VTForAll _ _ b $$ a = b (case a of
  TEInst a -> a
  TEApp  a -> a) -- FIXME: technically this should only ever be TEInst
_              $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (HasCallStack, Foldable t) => Type -> t TElim -> Type
($$*) = foldl' ($$)

infixl 9 $$, $$*


-- Patterns

data ValuePattern a
  = PWildcard
  | PVar a
  | PCon (Q Name :$ ValuePattern a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Pattern a
  = PEff (Q Name) (Stack (Pattern a)) a
  | PAll a
  | PVal (ValuePattern a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

pvar :: a -> Pattern a
pvar = PVal . PVar

pcon :: Q Name :$ ValuePattern a -> Pattern a
pcon = PVal . PCon


fill :: Traversable t => (b -> (b, c)) -> b -> t a -> (b, t c)
fill f = mapAccumL (const . f)

bindPattern :: Traversable t => Level -> t a -> (Level, t Type)
bindPattern = fill (\ d -> (succ d, free d))


-- Modules

-- FIXME: model operators and their associativities for parsing.
data Module = Module
  { name      :: MName
  -- FIXME: record source references to imports to contextualize ambiguous name errors.
  , imports   :: [Import]
  -- FIXME: record source references to operators to contextualize parse errors.
  , operators :: [(Op, Assoc)]
  -- FIXME: record source references to definitions to contextualize ambiguous name errors.
  , scope     :: Scope
  }

name_ :: Lens' Module MName
name_ = lens (\ Module{ name } -> name) (\ m name -> (m :: Module){ name })

imports_ :: Lens' Module [Import]
imports_ = lens imports (\ m imports -> m{ imports })

scope_ :: Lens' Module Scope
scope_ = lens scope (\ m scope -> m{ scope })


lookupC :: Alternative m => Name -> Module -> m (Q Name :=: Maybe Def ::: Type)
lookupC n Module{ name, scope } = maybe empty pure $ asum (matchDef <$> decls scope)
  where
  matchDef (d ::: _) = do
    n :=: v ::: _T <- maybe empty pure d >>= unDData >>= lookupScope n
    pure $ name:.:n :=: v ::: _T

-- | Look up effect operations.
lookupE :: Alternative m => Name -> Module -> m (Q Name :=: Maybe Def ::: Type)
lookupE n Module{ name, scope } = maybe empty pure $ asum (matchDef <$> decls scope)
  where
  matchDef (d ::: _) = do
    n :=: _ ::: _T <- maybe empty pure d >>= unDInterface >>= lookupScope n
    pure $ name:.:n :=: Nothing ::: _T

lookupD :: Alternative m => Name -> Module -> m (Q Name :=: Maybe Def ::: Type)
lookupD n Module{ name, scope } = maybe empty pure $ do
  d ::: _T <- Map.lookup n (decls scope)
  pure $ name:.:n :=: d ::: _T


newtype Scope = Scope { decls :: Map.Map Name (Maybe Def ::: Type) }
  deriving (Monoid, Semigroup)

decls_ :: Lens' Scope (Map.Map Name (Maybe Def ::: Type))
decls_ = coerced

scopeFromList :: [Name :=: Maybe Def ::: Type] -> Scope
scopeFromList = Scope . Map.fromList . map (\ (n :=: v ::: _T) -> (n, v ::: _T))

scopeToList :: Scope -> [Name :=: Maybe Def ::: Type]
scopeToList = map (\ (n, v ::: _T) -> n :=: v ::: _T) . Map.toList . decls

lookupScope :: Alternative m => Name -> Scope -> m (Name :=: Maybe Def ::: Type)
lookupScope n (Scope ds) = maybe empty (pure . (n :=:)) (Map.lookup n ds)


newtype Import = Import { name :: MName }


data Def
  = DTerm Expr
  | DData Scope
  | DInterface Scope
  | DModule Scope

unDData :: Alternative m => Def -> m Scope
unDData = \case
  DData cs -> pure cs
  _        -> empty

unDInterface :: Alternative m => Def -> m Scope
unDInterface = \case
  DInterface cs -> pure cs
  _             -> empty


-- Expressions

data TExpr
  = TVar (Var Index)
  | TType
  | TInterface
  | TString
  | TForAll Name TExpr TExpr
  | TArrow (Either Name [TExpr]) TExpr TExpr
  | TComp [TExpr] TExpr
  | TInst TExpr TExpr
  | TApp TExpr TExpr
  deriving (Eq, Ord, Show)

data Expr
  = XVar (Var Index)
  | XTLam Expr
  | XLam [(Pattern Name, Expr)]
  | XInst Expr TExpr
  | XApp Expr Expr
  | XCon (Q Name :$ Expr)
  | XString Text
  | XOp (Q Name) -- FIXME: this should have the arguments
  deriving (Eq, Ord, Show)


-- Quotation

quote :: Level -> Type -> TExpr
quote d = \case
  VKType         -> TType
  VKInterface    -> TInterface
  VTForAll n t b -> TForAll n (quote d t) (quote (succ d) (b (free d)))
  VTArrow n a b  -> TArrow (map (quote d) <$> n) (quote d a) (quote d b)
  VTComp s t     -> TComp (quote d <$> s) (quote d t)
  VTNe (n :$ sp) -> foldl' (\ head -> \case
    TEInst a -> TInst head (quote d a)
    TEApp  a -> TApp head (quote d a)) (TVar (levelToIndex d <$> n)) sp
  VTString       -> TString

eval :: HasCallStack => Stack Type -> IntMap.IntMap Type -> TExpr -> Type
eval env subst = \case
  TVar v        -> unVar global ((env !) . getIndex) (\ m -> fromMaybe (metavar m) (IntMap.lookup (getMeta m) subst)) v
  TType         -> VKType
  TInterface    -> VKInterface
  TForAll n t b -> VTForAll n (eval env subst t) (\ v -> eval (env :> v) subst b)
  TArrow n a b  -> VTArrow (map (eval env subst) <$> n) (eval env subst a) (eval env subst b)
  TComp s t     -> VTComp (eval env subst <$> s) (eval env subst t)
  TInst f a     -> eval env subst f $$ TEInst (eval env subst a)
  TApp  f a     -> eval env subst f $$ TEApp (eval env subst a)
  TString       -> VTString
