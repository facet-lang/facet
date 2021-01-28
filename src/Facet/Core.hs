module Facet.Core
( -- * Types
  Type(..)
, TElim(..)
, unBind
, unBind'
, Sig(..)
, effectVar_
, interfaces_
, Binding(..)
, icit_
, type_
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
, Pattern(..)
, fill
, bindPattern
, unsafeUnPVar
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
import           Data.Text (Text)
import           Data.Traversable (mapAccumL)
import           Facet.Name hiding (bind)
import           Facet.Stack
import           Facet.Syntax
import           GHC.Stack
import           Prelude hiding (zip, zipWith)

-- Types

data Type
  = VKType
  | VKInterface
  | VTForAll (Binding Type) (Type -> Type)
  | VTArrow Type Type
  | VTNe (Var Level :$ TElim)
  | VTComp (Sig Type) Type
  | VTString

data TElim
  = TEInst Type
  | TEApp Type

unBind :: Alternative m => Type -> m (Binding Type, Type -> Type)
unBind = \case{ VTForAll t b -> pure (t, b) ; _ -> empty }

-- | A variation on 'unBind' which can be conveniently chained with 'splitr' to strip a prefix of quantifiers off their eventual body.
unBind' :: Alternative m => (Level, Type) -> m (Binding Type, (Level, Type))
unBind' (d, v) = fmap (\ _B -> (succ d, _B (free d))) <$> unBind v


data Sig a = Sig
  { effectVar  :: a
  , interfaces :: [a]
  }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

effectVar_ :: Lens' (Sig a) a
effectVar_ = lens effectVar (\ s effectVar -> s{ effectVar })

interfaces_ :: Lens' (Sig a) [a]
interfaces_ = lens interfaces (\ s interfaces -> s{ interfaces })


data Binding a = Binding
  { icit  :: Icit
  , name  :: Maybe Name
  , type' :: a
  }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

icit_ :: Lens' (Binding a) Icit
icit_ = lens icit (\ b icit -> b{ icit })

type_ :: Lens' (Binding a) a
type_ = lens type' (\ b type' -> b{ type' })


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
    VTForAll t b   -> binding d t || go (succ d) (b (free d))
    VTArrow a b    -> go d a || go d b
    VTComp s t     -> sig d s || go d t
    VTNe (h :$ sp) -> p h || any (elim d) sp
    VTString       -> False

  elim d = \case
    TEInst t -> go d t
    TEApp  t -> go d t

  binding d (Binding _ _ t) = go d t

  sig d (Sig v s) = go d v || any (go d) s


-- Elimination

($$) :: HasCallStack => Type -> TElim -> Type
VTNe (h :$ es) $$ a = VTNe (h :$ (es :> a))
VTForAll _ b   $$ a = b (case a of
  TEInst a -> a
  TEApp  a -> a) -- FIXME: technically this should only ever be TEInst
_              $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (HasCallStack, Foldable t) => Type -> t TElim -> Type
($$*) = foldl' ($$)

infixl 9 $$, $$*


-- Patterns

-- FIXME: is there any point to splitting this into separate value and effect patterns?
data Pattern a
  = PVar a
  | PCon (Q Name :$ Pattern a)
  | PEff (Q Name) (Stack (Pattern a)) a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

fill :: Traversable t => (b -> (b, c)) -> b -> t a -> (b, t c)
fill f = mapAccumL (const . f)

bindPattern :: Traversable t => Level -> t a -> (Level, t Type)
bindPattern = fill (\ d -> (succ d, free d))

unsafeUnPVar :: HasCallStack => Pattern a -> a
unsafeUnPVar = \case
  PVar a -> a
  _      -> error "unsafeUnPVar: non-PVar pattern"


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
  | TForAll (Binding TExpr) TExpr
  | TArrow TExpr TExpr
  | TComp (Sig TExpr) TExpr
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
  VTForAll t b   -> TForAll (quote d <$> t) (quote (succ d) (b (free d)))
  VTArrow a b    -> TArrow (quote d a) (quote d b)
  VTComp s t     -> TComp (quote d <$> s) (quote d t)
  VTNe (n :$ sp) -> foldl' (\ head -> \case
    TEInst a -> TInst head (quote d a)
    TEApp  a -> TApp head (quote d a)) (TVar (levelToIndex d <$> n)) sp
  VTString       -> TString

eval :: HasCallStack => Stack Type -> IntMap.IntMap Type -> TExpr -> Type
eval env metas = \case
  TVar v      -> unVar global ((env !) . getIndex) metavar v
  TType       -> VKType
  TInterface  -> VKInterface
  TForAll t b -> VTForAll (eval env metas <$> t) (\ v -> eval (env :> v) metas b)
  TArrow a b  -> VTArrow (eval env metas a) (eval env metas b)
  TComp s t   -> VTComp (eval env metas <$> s) (eval env metas t)
  TInst f a   -> eval env metas f $$ TEInst (eval env metas a)
  TApp  f a   -> eval env metas f $$ TEApp (eval env metas a)
  TString     -> VTString
