module Facet.Core
( -- * Values
  Value(..)
, Type
, Expr
, Comp(..)
, bindComp
, bindsComp
, unBind
, unBind'
, unLam
, Sig(..)
, effectVar_
, interfaces_
, Clause(..)
, instantiateClause
, Binding(..)
  -- ** Variables
, Var(..)
, unVar
, global
, free
, occursIn
  -- ** Elimination
, ($$)
, ($$*)
, case'
, match
  -- ** Substitution
, bind
, binds
, Subst
, emptySubst
, insertSubst
  -- ** Classification
, Sort(..)
, sortOf
, sortOfComp
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
, QComp(..)
, quote
, quoteComp
, eval
, evalComp
) where

import           Control.Applicative (Alternative(..))
import           Control.Lens (Lens', coerced, lens)
import           Control.Monad (guard)
import           Data.Foldable (asum, foldl', toList)
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
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
  | TSusp Comp
  | ELam Pl [Clause]
  -- | Neutral terms are an unreduced head followed by a stack of eliminators.
  | VNe (Var Level :$ (Pl, Value))
  | ECon (Q Name :$ Expr)
  | TString
  | EString Text
  -- | Effect operation and its parameters.
  | EOp (Q Name :$ (Pl, Expr))

type Type = Value
type Expr = Value


-- | A computation type, represented as a (possibly polymorphic) telescope with signatures on every argument and return.
data Comp
  = TForAll (Binding Type) (Type -> Comp)
  | TRet (Sig Value) Type

substCompWith :: (Var Level -> Value) -> Comp -> Comp
substCompWith f = go
  where
  go = \case
    TForAll t b -> TForAll (binding t) (go . b)
    TRet s t    -> TRet (sig s) (substWith f t)

  binding (Binding p n s t) = Binding p n (map (substWith f) <$> s) (substWith f t)
  sig (Sig v s) = Sig (substWith f <$> v) (map (substWith f) s)

bindComp :: Level -> Value -> Comp -> Comp
bindComp k v = bindsComp (IntMap.singleton (getLevel k) v)

bindsComp :: IntMap.IntMap Value -> Comp -> Comp
bindsComp s
  | IntMap.null s = id
  | otherwise     = substCompWith (substFree s)


unBind :: Alternative m => Comp -> m (Binding Value, Value -> Comp)
unBind = \case{ TForAll t b -> pure (t, b) ; _ -> empty }

-- | A variation on 'unBind' which can be conveniently chained with 'splitr' to strip a prefix of quantifiers off their eventual body.
unBind' :: Alternative m => (Level, Comp) -> m (Binding Value, (Level, Comp))
unBind' (d, v) = fmap (\ _B -> (succ d, _B (free d))) <$> unBind v


unLam :: Alternative m => Value -> m (Pl, [Clause])
unLam = \case{ ELam n b -> pure (n, b) ; _ -> empty }


data Sig a = Sig
  { effectVar  :: Maybe a
  , interfaces :: [a]
  }
  deriving (Foldable, Functor, Traversable)

effectVar_ :: Lens' (Sig a) (Maybe a)
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
  { pl    :: Pl
  , name  :: Maybe Name
  , delta :: Maybe [a]
  , type' :: a
  }
  deriving (Foldable, Functor, Traversable)


-- Variables

data Var a
  = Global (Q Name) -- ^ Global variables, considered equal by 'QName'.
  | Free a
  deriving (Foldable, Functor, Traversable)

instance Eq a => Eq (Var a) where
  (==) = curry $ \case
    (Global  q1, Global  q2) -> q1 == q2
    (Global  _,  _)          -> False
    (Free    l1, Free    l2) -> l1 == l2
    (Free    _,  _)          -> False

instance Ord a => Ord (Var a) where
  compare = curry $ \case
    (Global  q1, Global  q2) -> q1 `compare` q2
    (Global  _,  _)          -> LT
    (Free    l1, Free    l2) -> l1 `compare` l2
    (Free    _,  _)          -> LT

unVar :: (Q Name -> b) -> (a -> b) -> Var a -> b
unVar f g = \case
  Global  n -> f n
  Free    n -> g n


global :: Q Name -> Value
global = var . Global

free :: Level -> Value
free = var . Free


var :: Var Level -> Value
var = VNe . (:$ Nil)


occursIn :: (Var Level -> Bool) -> Value -> Bool
occursIn p = go (Level 0) -- FIXME: this should probably be doing something more sensible
  where
  go d = \case
    KType          -> False
    KInterface     -> False
    TSusp c        -> comp d c
    ELam _ cs      -> any (clause d) cs
    VNe (h :$ sp)  -> p h || any (any (go d)) sp
    ECon (_ :$ sp) -> any (go d) sp
    TString        -> False
    EString _      -> False
    EOp (_ :$ sp)  -> any (any (go d)) sp

  comp d = \case
    TForAll t b -> binding d t || comp (succ d) (b (free d))
    TRet s t    -> sig d s || go d t
  binding d (Binding _ _ s t) = any (any (go d)) s || go d t
  sig d (Sig v s) = any (go d) v || any (go d) s
  clause d (Clause p b) = let (d', p') = fill (\ d -> (succ d, free d)) d p in go d' (b p')


-- Elimination

($$) :: HasCallStack => Value -> (Pl, Value) -> Value
VNe (h :$ es) $$ a = VNe (h :$ (es :> a))
EOp (q :$ es) $$ a = EOp (q :$ (es :> a))
TSusp t       $$ a
  | TForAll _ b <- t = case b (snd a) of
    -- FIXME: it’s not clear to me that it’s ok to discard the signature.
    -- maybe this should still be a nullary computation which gets eliminated with !.
    TRet _ t -> t
    t        -> TSusp t
ELam _ b      $$ a = case' (snd a) b
_             $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (HasCallStack, Foldable t) => Value -> t (Pl, Value) -> Value
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


-- Substitution

substWith :: (Var Level -> Value) -> Value -> Value
substWith f = go
  where
  go = \case
    KType         -> KType
    KInterface    -> KInterface
    TSusp t       -> TSusp (substCompWith f t)
    ELam p b      -> ELam p (map clause b)
    VNe (v :$ a)  -> f v $$* fmap (fmap go) a
    ECon c        -> ECon (fmap go c)
    TString       -> TString
    EString s     -> EString s
    EOp (q :$ sp) -> EOp (q :$ fmap (fmap go) sp)

  clause (Clause p b) = Clause p (go . b)

-- | TForAll a free variable.
bind :: Level -> Value -> Value -> Value
bind k v = binds (IntMap.singleton (getLevel k) v)

binds :: IntMap.IntMap Value -> Value -> Value
binds s
  | IntMap.null s = id
  | otherwise     = substWith (substFree s)

substFree :: IntMap.IntMap Value -> Var Level -> Value
substFree s = unVar global (\ v -> fromMaybe (free v) (IntMap.lookup (getLevel v) s))


type Subst = IntMap.IntMap (Maybe Value ::: Type)

emptySubst :: Subst
emptySubst = IntMap.empty

insertSubst :: Meta -> Maybe Value ::: Type -> Subst -> Subst
insertSubst n (v ::: _T) = IntMap.insert (getMeta n) (v ::: _T)


-- Classification

data Sort
  = STerm
  | SType
  | SKind
  deriving (Bounded, Enum, Eq, Ord, Show)

-- | Classifies values according to whether or not they describe types.
sortOf :: Stack Sort -> Value -> Sort
sortOf ctx = \case
  KType         -> SKind
  KInterface    -> SKind
  TSusp t       -> sortOfComp ctx t
  ELam{}        -> STerm
  VNe (h :$ sp) -> minimum (unVar (const SType) ((ctx !) . getIndex . levelToIndex (Level (length ctx))) h : toList (sortOf ctx . snd <$> sp))
  ECon _        -> STerm
  TString       -> SType
  EString _     -> STerm
  EOp _         -> STerm -- FIXME: will this always be true?

sortOfComp :: Stack Sort -> Comp -> Sort
sortOfComp ctx = \case
  TForAll (Binding _ _ _ _T) _B -> let _T' = sortOf ctx _T in min _T' (sortOfComp (ctx :> _T') (_B (free (Level (length ctx)))))
  TRet _ _T                     -> sortOf ctx _T


-- Patterns

-- FIXME: is there any point to splitting this into separate value and effect patterns?
data Pattern a
  = PVar a
  | PCon (Q Name :$ Pattern a)
  | PEff (Q Name) (Stack (Pattern a)) a
  deriving (Foldable, Functor, Traversable)

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


lookupC :: Alternative m => Name -> Module -> m (Q Name :=: Maybe Def ::: Comp)
lookupC n Module{ name, scope } = maybe empty pure $ asum (matchDef <$> decls scope)
  where
  matchDef (d ::: _) = do
    n :=: v ::: _T <- maybe empty pure d >>= unDData >>= lookupScope n
    pure $ name:.:n :=: v ::: _T

-- | Look up effect operations.
lookupE :: Alternative m => Name -> Module -> m (Q Name :=: Maybe Def ::: Comp)
lookupE n Module{ name, scope } = maybe empty pure $ asum (matchDef <$> decls scope)
  where
  matchDef (d ::: _) = do
    n :=: _ ::: _T <- maybe empty pure d >>= unDInterface >>= lookupScope n
    pure $ name:.:n :=: Nothing ::: _T

lookupD :: Alternative m => Name -> Module -> m (Q Name :=: Maybe Def ::: Comp)
lookupD n Module{ name, scope } = maybe empty pure $ do
  d ::: _T <- Map.lookup n (decls scope)
  pure $ name:.:n :=: d ::: _T


newtype Scope = Scope { decls :: Map.Map Name (Maybe Def ::: Comp) }
  deriving (Monoid, Semigroup)

decls_ :: Lens' Scope (Map.Map Name (Maybe Def ::: Comp))
decls_ = coerced

scopeFromList :: [Name :=: Maybe Def ::: Comp] -> Scope
scopeFromList = Scope . Map.fromList . map (\ (n :=: v ::: _T) -> (n, v ::: _T))

scopeToList :: Scope -> [Name :=: Maybe Def ::: Comp]
scopeToList = map (\ (n, v ::: _T) -> (n :=: v ::: _T)) . Map.toList . decls

lookupScope :: Alternative m => Name -> Scope -> m (Name :=: Maybe Def ::: Comp)
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
  | QTSusp QComp
  | QELam Pl [(Pattern Name, Quote)]
  | QApp Quote (Pl, Quote)
  | QECon (Q Name :$ Quote)
  | QTString
  | QEString Text
  | QEOp (Q Name)

data QComp = QComp [Binding Quote] (Sig Quote) Quote

quote :: Level -> Value -> Quote
quote d = \case
  KType          -> QKType
  KInterface     -> QKInterface
  TSusp c        -> QTSusp (quoteComp d c)
  ELam p cs      -> QELam p (map (clause d) cs)
  VNe (n :$ sp)  -> foldl' QApp (QVar (levelToIndex d <$> n)) (fmap (quote d) <$> sp)
  ECon (n :$ sp) -> QECon (n :$ (quote d <$> sp))
  TString        -> QTString
  EString s      -> QEString s
  EOp (n :$ sp)  -> foldl' QApp (QEOp n) (fmap (quote d) <$> sp)
  where
  clause d (Clause p b) = let (d', p') = fill (\ d -> (d, free d)) d p in (p, quote d' (b p'))

quoteComp :: Level -> Comp -> QComp
quoteComp d c = go d c QComp
  where
  go d = \case
    TForAll t b -> \ k -> go (succ d) (b (free d)) $ \ b s t' -> k ((quote d <$> t):b) s t'
    TRet s t    -> \ k -> k [] (quote d <$> s) (quote d t)

eval :: Stack (Maybe Value) -> Quote -> Value
eval env = \case
  QVar v          -> unVar global (\ i -> fromMaybe (free (indexToLevel (Level (length env)) i)) (env ! getIndex i)) v
  QKType          -> KType
  QKInterface     -> KInterface
  QTSusp c        -> TSusp $ evalComp env c
  QELam p cs      -> ELam p $ map (\ (p, b) -> Clause p (\ p -> eval (foldl' (\ env v -> env :> Just v) env p) b)) cs
  QApp f a        -> eval env f $$ (eval env <$> a)
  QECon (n :$ sp) -> ECon $ n :$ (eval env <$> sp)
  QTString        -> TString
  QEString s      -> EString s
  QEOp n          -> EOp $ n :$ Nil

evalComp :: Stack (Maybe Value) -> QComp -> Comp
evalComp env (QComp bs s t) = foldr (\ t b env -> TForAll (eval env <$> t) (\ v -> b (env :> Just v))) (\ env -> TRet (eval env <$> s) (eval env t)) bs env
