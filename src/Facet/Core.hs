module Facet.Core
( -- * Values
  Value(..)
, Type
, Expr
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
, Quote(..)
, quote
, eval
) where

import           Control.Applicative (Alternative(..))
import           Control.Lens (Lens', coerced, lens)
import           Control.Monad (guard)
import           Data.Foldable (asum, foldl', toList)
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import           Data.Semialign
import           Data.Text (Text)
import           Data.Traversable (mapAccumL)
import           Facet.Name hiding (bind)
import           Facet.Stack
import           Facet.Syntax
import           GHC.Stack
import           Prelude hiding (zip, zipWith)

-- Values

data Value
  = KType
  | KInterface
  | TForAll (Binding Type) (Type -> Type)
  | TComp (Sig Type) Type
  | ELam Icit [Clause]
  -- | Neutral terms are an unreduced head followed by a stack of eliminators.
  | VNe (Var Level :$ (Icit, Value))
  | ECon (Q Name :$ Expr)
  | TString
  | EString Text
  -- | Effect operation and its parameters.
  | EOp (Q Name :$ (Icit, Expr))

type Type = Value
type Expr = Value


unBind :: Alternative m => Type -> m (Binding Type, Type -> Type)
unBind = \case{ TForAll t b -> pure (t, b) ; _ -> empty }

-- | A variation on 'unBind' which can be conveniently chained with 'splitr' to strip a prefix of quantifiers off their eventual body.
unBind' :: Alternative m => (Level, Type) -> m (Binding Type, (Level, Type))
unBind' (d, v) = fmap (\ _B -> (succ d, _B (free d))) <$> unBind v


unLam :: Alternative m => Value -> m (Icit, [Clause])
unLam = \case{ ELam n b -> pure (n, b) ; _ -> empty }


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
  , branch  :: Pattern Value -> Value
  }

instantiateClause :: Level -> Clause -> (Level, Value)
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


global :: Q Name -> Value
global = var . Global

free :: Level -> Value
free = var . Free

metavar :: Meta -> Value
metavar = var . Metavar


var :: Var Level -> Value
var = VNe . (:$ Nil)


occursIn :: (Var Level -> Bool) -> Level -> Value -> Bool
occursIn p = go
  where
  go d = \case
    KType          -> False
    KInterface     -> False
    TForAll t b    -> binding d t || go (succ d) (b (free d))
    TComp s t      -> sig d s || go d t
    ELam _ cs      -> any (clause d) cs
    VNe (h :$ sp)  -> p h || any (any (go d)) sp
    ECon (_ :$ sp) -> any (go d) sp
    TString        -> False
    EString _      -> False
    EOp (_ :$ sp)  -> any (any (go d)) sp

  binding d (Binding _ _ t) = go d t
  sig d (Sig v s) = go d v || any (go d) s
  clause d (Clause p b) = let (d', p') = fill (\ d -> (succ d, free d)) d p in go d' (b p')


-- Elimination

($$) :: HasCallStack => Value -> (Icit, Value) -> Value
VNe (h :$ es) $$ a = VNe (h :$ (es :> a))
EOp (q :$ es) $$ a = EOp (q :$ (es :> a))
TForAll _ b   $$ a = b (snd a)
ELam _ b      $$ a = case' (snd a) b
_             $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (HasCallStack, Foldable t) => Value -> t (Icit, Value) -> Value
($$*) = foldl' ($$)

infixl 9 $$, $$*


case' :: HasCallStack => Value -> [Clause] -> Value
case' s cs = case asum ((\ (Clause p f) -> f <$> match s p) <$> cs) of
  Just v -> v
  _      -> error "non-exhaustive patterns in lambda"

match :: Value -> Pattern b -> Maybe (Pattern Value)
match = curry $ \case
  -- FIXME: this shouldn’t match computations
  (s,               PVar _)         -> Just (PVar s)
  (ECon (n' :$ fs), PCon (n :$ ps)) -> do
    guard (n == n')
    -- NB: we’re assuming they’re the same length because they’ve passed elaboration.
    PCon . (n' :$) <$> sequenceA (zipWith match fs ps)
  (_,               PCon _)         -> Nothing
  -- FIXME: match effect patterns against computations (?)
  (_,               PEff{})         -> Nothing


-- Classification

data Sort
  = STerm
  | SType
  | SKind
  deriving (Bounded, Enum, Eq, Ord, Show)

-- | Classifies values according to whether or not they describe types.
sortOf :: Stack Sort -> Value -> Sort
sortOf ctx = \case
  KType                       -> SKind
  KInterface                  -> SKind
  TForAll (Binding _ _ _T) _B -> let _T' = sortOf ctx _T in min _T' (sortOf (ctx :> _T') (_B (free (Level (length ctx)))))
  TComp _ _T                  -> sortOf ctx _T
  ELam{}                      -> STerm
  VNe (h :$ sp)               -> minimum (unVar (const SType) ((ctx !) . getIndex . levelToIndex (Level (length ctx))) (const SType) h : toList (sortOf ctx . snd <$> sp))
  ECon _                      -> STerm
  TString                     -> SType
  EString _                   -> STerm
  EOp _                       -> STerm -- FIXME: will this always be true?


-- Patterns

-- FIXME: is there any point to splitting this into separate value and effect patterns?
data Pattern a
  = PVar a
  | PCon (Q Name :$ Pattern a)
  | PEff (Q Name) (Stack (Pattern a)) a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

fill :: Traversable t => (b -> (b, c)) -> b -> t a -> (b, t c)
fill f = mapAccumL (const . f)

bindPattern :: Traversable t => Level -> t a -> (Level, t Value)
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
  = DTerm Value
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

data Quote
  = QVar (Var Index)
  | QKType
  | QKInterface
  | QTForAll (Binding Quote) Quote
  | QTComp (Sig Quote) Quote
  | QELam Icit [(Pattern Name, Quote)]
  | QApp Quote (Icit, Quote)
  | QECon (Q Name :$ Quote)
  | QTString
  | QEString Text
  | QEOp (Q Name)
  deriving (Eq, Ord, Show)

quote :: Level -> Value -> Quote
quote d = \case
  KType          -> QKType
  KInterface     -> QKInterface
  TForAll t b    -> QTForAll (quote d <$> t) (quote (succ d) (b (free d)))
  TComp s t      -> QTComp (quote d <$> s) (quote d t)
  ELam p cs      -> QELam p (map (clause d) cs)
  VNe (n :$ sp)  -> foldl' QApp (QVar (levelToIndex d <$> n)) (fmap (quote d) <$> sp)
  ECon (n :$ sp) -> QECon (n :$ (quote d <$> sp))
  TString        -> QTString
  EString s      -> QEString s
  EOp (n :$ sp)  -> foldl' QApp (QEOp n) (fmap (quote d) <$> sp)
  where
  clause d (Clause p b) = let (d', p') = fill (\ d -> (d, free d)) d p in (p, quote d' (b p'))

eval :: HasCallStack => Stack Value -> IntMap.IntMap Value -> Quote -> Value
eval env metas = \case
  QVar v          -> unVar global ((env !) . getIndex) metavar v
  QKType          -> KType
  QKInterface     -> KInterface
  QTForAll t b    -> TForAll (eval env metas <$> t) (\ v -> eval (env :> v) metas b)
  QTComp s t      -> TComp (eval env metas <$> s) (eval env metas t)
  QELam p cs      -> ELam p $ map (\ (p, b) -> Clause p (\ p -> eval (foldl' (:>) env p) metas b)) cs
  QApp f a        -> eval env metas f $$ (eval env metas <$> a)
  QECon (n :$ sp) -> ECon $ n :$ (eval env metas <$> sp)
  QTString        -> TString
  QEString s      -> EString s
  QEOp n          -> EOp $ n :$ Nil
