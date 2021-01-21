{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module Facet.Core
( -- * Values
  Value(..)
, Elim(..)
, Type
, Term
, unBind
, unBind'
, unLam
, Sig(..)
, effectVar_
, interfaces_
, Clause(..)
, instantiateClause
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
, case'
, match
  -- ** Classification
, Sort(..)
, sortOf
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
  -- * Quotation
, Expr(..)
, quote
, eval
) where

import           Control.Applicative (Alternative(..))
import           Control.Lens (Lens', coerced, lens)
import           Control.Monad (guard)
import           Data.Foldable (asum, foldl', toList)
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import           Data.Semialign.Exts
import           Data.Text (Text)
import           Data.Traversable (mapAccumL)
import           Facet.Name hiding (bind)
import           Facet.Stack
import           Facet.Syntax
import           GHC.Stack
import           Prelude hiding (zip, zipWith)

-- Values

data Value sort where
  VKType :: Value Type
  VKInterface :: Value Type
  VTForAll :: Binding (Value Type) -> (Value Type -> Value Type) -> Value Type
  VTComp :: Sig (Value Type) -> Value Type -> Value Type
  VETLam :: (Value Type -> Value Term) -> Value Term
  VELam :: [Clause] -> Value Term
  -- | Neutral terms are an unreduced head followed by a stack of eliminators.
  VNe :: Var Level :$ Elim sort -> Value sort
  VECon :: Q Name :$ Elim Term -> Value Term
  VTString :: Value Type
  VEString :: Text -> Value Term
  -- | Effect operation and its parameters.
  VEOp :: Q Name :$ Elim Term -> Value Term

data Elim sort
  = EExApp (Value sort)
  | EImApp (Value Type)

unBind :: Alternative m => Value Type -> m (Binding (Value Type), Value Type -> Value Type)
unBind = \case{ VTForAll t b -> pure (t, b) ; _ -> empty }

-- | A variation on 'unBind' which can be conveniently chained with 'splitr' to strip a prefix of quantifiers off their eventual body.
unBind' :: Alternative m => (Level, Value Type) -> m (Binding (Value Type), (Level, Value Type))
unBind' (d, v) = fmap (\ _B -> (succ d, _B (free d))) <$> unBind v


unLam :: Alternative m => Value Term -> m [Clause]
unLam = \case{ VELam b -> pure b ; _ -> empty }


data Sig a = Sig
  { effectVar  :: a
  , interfaces :: [a]
  }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

effectVar_ :: Lens' (Sig a) a
effectVar_ = lens effectVar (\ s effectVar -> s{ effectVar })

interfaces_ :: Lens' (Sig a) [a]
interfaces_ = lens interfaces (\ s interfaces -> s{ interfaces })


data Clause = Clause
  { pattern :: Pattern Name
  , branch  :: Pattern (Value Term) -> Value Term
  }

instantiateClause :: Level -> Clause -> (Level, Value Term)
instantiateClause d (Clause p b) = b <$> bindPattern d p


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


global :: Q Name -> Value sort
global = var . Global

free :: Level -> Value sort
free = var . Free

metavar :: Meta -> Value sort
metavar = var . Metavar


var :: Var Level -> Value sort
var = VNe . (:$ Nil)


occursIn :: (Var Level -> Bool) -> Level -> Value sort -> Bool
occursIn p = go
  where
  go :: Level -> Value sort -> Bool
  go d = \case
    VKType          -> False
    VKInterface     -> False
    VTForAll t b    -> binding d t || go (succ d) (b (free d))
    VTComp s t      -> sig d s || go d t
    VETLam b        -> go (succ d) (b (free d))
    VELam cs        -> any (clause d) cs
    VNe (h :$ sp)   -> p h || any (elim d) sp
    VECon (_ :$ sp) -> any (elim d) sp
    VTString        -> False
    VEString _      -> False
    VEOp (_ :$ sp)  -> any (elim d) sp

  elim :: Level -> Elim sort -> Bool
  elim d = \case
    EExApp a -> go d a
    EImApp a -> go d a
  binding :: Level -> Binding (Value Type) -> Bool
  binding d (Binding _ _ t) = go d t
  sig :: Level -> Sig (Value Type) -> Bool
  sig d (Sig v s) = go d v || any (go d) s
  clause d (Clause p b) = let (d', p') = fill (\ d -> (succ d, free d)) d p in go d' (b p')


-- Elimination

-- ($$$) :: HasCallStack => Value Type -> (Icit, Value Type) -> Value Type
-- VNe (h :$ es) $$$ a = VNe (h :$ (es :> a))



($$) :: HasCallStack => Value sort -> Elim sort -> Value sort
VNe  (h :$ es) $$ a = VNe (h :$ (es :> a))
VEOp (q :$ es) $$ a = VEOp (q :$ (es :> a))
VTForAll _ b   $$ a = b (case a of
  EExApp a -> a
  EImApp a -> a)
VETLam b       $$ a = case a of
  EExApp a -> _
  EImApp a -> b a
VELam b        $$ a = case a of
  EExApp a -> case' a b
  EImApp a -> _
_              $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (HasCallStack, Foldable t) => Value sort -> t (Elim sort) -> Value sort
($$*) = foldl' ($$)

infixl 9 $$, $$*


case' :: HasCallStack => Value Term -> [Clause] -> Value Term
case' s cs = case asum ((\ (Clause p f) -> f <$> match s p) <$> cs) of
  Just v -> v
  _      -> error "non-exhaustive patterns in lambda"

match :: Value Term -> Pattern b -> Maybe (Pattern (Value Term))
match = curry $ \case
  -- FIXME: this shouldn’t match computations
  (s,                PVar _)         -> Just (PVar s)
  (VECon (n' :$ fs), PCon (n :$ ps)) -> do
    guard (n == n')
    -- NB: we’re assuming they’re the same length because they’ve passed elaboration.
    PCon . (n' :$) <$> zipWithM match fs ps
  (_,                PCon _)         -> Nothing
  -- FIXME: match effect patterns against computations (?)
  (_,                PEff{})         -> Nothing


-- Classification

data Sort
  = STerm
  | SType
  | SKind
  deriving (Bounded, Enum, Eq, Ord, Show)

-- | Classifies values according to whether or not they describe types.
sortOf :: Stack Sort -> Value sort -> Sort
sortOf ctx = \case
  VKType                       -> SKind
  VKInterface                  -> SKind
  VTForAll (Binding _ _ _T) _B -> let _T' = sortOf ctx _T in min _T' (sortOf (ctx :> _T') (_B (free (Level (length ctx)))))
  VTComp _ _T                  -> sortOf ctx _T
  VETLam{}                     -> STerm
  VELam{}                      -> STerm
  VNe (h :$ sp)                -> minimum (unVar (const SType) ((ctx !) . getIndex . levelToIndex (Level (length ctx))) (const SType) h : toList (elim ctx <$> sp))
  VECon _                      -> STerm
  VTString                     -> SType
  VEString _                   -> STerm
  VEOp _                       -> STerm -- FIXME: will this always be true?
  where
  elim :: Stack Sort -> Elim sort -> Sort
  elim ctx = \case
    EExApp a -> sortOf ctx a
    EImApp a -> sortOf ctx a


-- Patterns

-- FIXME: is there any point to splitting this into separate value and effect patterns?
data Pattern a
  = PVar a
  | PCon (Q Name :$ Pattern a)
  | PEff (Q Name) (Stack (Pattern a)) a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

fill :: Traversable t => (b -> (b, c)) -> b -> t a -> (b, t c)
fill f = mapAccumL (const . f)

bindPattern :: Traversable t => Level -> t a -> (Level, t (Value Term))
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


lookupC :: Alternative m => Name -> Module -> m (Q Name :=: Maybe Def ::: Value Type)
lookupC n Module{ name, scope } = maybe empty pure $ asum (matchDef <$> decls scope)
  where
  matchDef (d ::: _) = do
    n :=: v ::: _T <- maybe empty pure d >>= unDData >>= lookupScope n
    pure $ name:.:n :=: v ::: _T

-- | Look up effect operations.
lookupE :: Alternative m => Name -> Module -> m (Q Name :=: Maybe Def ::: Value Type)
lookupE n Module{ name, scope } = maybe empty pure $ asum (matchDef <$> decls scope)
  where
  matchDef (d ::: _) = do
    n :=: _ ::: _T <- maybe empty pure d >>= unDInterface >>= lookupScope n
    pure $ name:.:n :=: Nothing ::: _T

lookupD :: Alternative m => Name -> Module -> m (Q Name :=: Maybe Def ::: Value Type)
lookupD n Module{ name, scope } = maybe empty pure $ do
  d ::: _T <- Map.lookup n (decls scope)
  pure $ name:.:n :=: d ::: _T


newtype Scope = Scope { decls :: Map.Map Name (Maybe Def ::: Value Type) }
  deriving (Monoid, Semigroup)

decls_ :: Lens' Scope (Map.Map Name (Maybe Def ::: Value Type))
decls_ = coerced

scopeFromList :: [Name :=: Maybe Def ::: Value Type] -> Scope
scopeFromList = Scope . Map.fromList . map (\ (n :=: v ::: _T) -> (n, v ::: _T))

scopeToList :: Scope -> [Name :=: Maybe Def ::: Value Type]
scopeToList = map (\ (n, v ::: _T) -> n :=: v ::: _T) . Map.toList . decls

lookupScope :: Alternative m => Name -> Scope -> m (Name :=: Maybe Def ::: Value Type)
lookupScope n (Scope ds) = maybe empty (pure . (n :=:)) (Map.lookup n ds)


newtype Import = Import { name :: MName }


data Def
  = DTerm (Value Term)
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


-- Quotation

data Expr sort where
  XVar :: Var Index -> Expr sort
  XKType :: Expr Type
  XKInterface :: Expr Type
  XTForAll :: Binding (Expr Type) -> Expr Type -> Expr Type
  XTComp :: Sig (Expr Type) -> Expr Type -> Expr Type
  XETLam :: Expr Type -> Expr Term
  XELam :: [(Pattern Name, Expr Term)] -> Expr Term
  XApp :: Expr sort -> (Icit, Expr sort) -> Expr sort
  XECon :: Q Name :$ Expr Term -> Expr Term
  XTString :: Expr Type
  XEString :: Text -> Expr Term
  XEOp :: Q Name -> Expr Term

deriving instance Eq   (Expr sort)
deriving instance Ord  (Expr sort)
deriving instance Show (Expr sort)

quote :: Level -> Value sort -> Expr sort
quote d = \case
  VKType          -> XKType
  VKInterface     -> XKInterface
  VTForAll t b    -> XTForAll (quote d <$> t) (quote (succ d) (b (free d)))
  VTComp s t      -> XTComp (quote d <$> s) (quote d t)
  VETLam b        -> XETLam (quote (succ d) (b (free d)))
  VELam cs        -> XELam (map (clause d) cs)
  VNe (n :$ sp)   -> foldl' XApp (XVar (levelToIndex d <$> n)) (fmap (quote d) <$> sp)
  VECon (n :$ sp) -> XECon (n :$ (quote d <$> sp))
  VTString        -> XTString
  VEString s      -> XEString s
  VEOp (n :$ sp)  -> foldl' XApp (XEOp n) (fmap (quote d) <$> sp)
  where
  clause d (Clause p b) = let (d', p') = fill (\ d -> (d, free d)) d p in (p, quote d' (b p'))

eval :: HasCallStack => Stack (Value sort) -> IntMap.IntMap (Value sort) -> Expr sort -> Value sort
eval env metas = \case
  XVar v          -> unVar global ((env !) . getIndex) metavar v
  XKType          -> VKType
  XKInterface     -> VKInterface
  XTForAll t b    -> VTForAll (eval env metas <$> t) (\ v -> eval (env :> v) metas b)
  XTComp s t      -> VTComp (eval env metas <$> s) (eval env metas t)
  XETLam b        -> VETLam (\ v -> eval (env :> v) metas b)
  XELam cs        -> VELam $ map (\ (p, b) -> Clause p (\ p -> eval (foldl' (:>) env p) metas b)) cs
  XApp f a        -> eval env metas f $$ (eval env metas <$> a)
  XECon (n :$ sp) -> VECon $ n :$ (eval env metas <$> sp)
  XTString        -> VTString
  XEString s      -> VEString s
  XEOp n          -> VEOp $ n :$ Nil
