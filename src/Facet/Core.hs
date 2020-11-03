module Facet.Core
( -- * Values
  Value(..)
, Type
, Expr
, Comp(..)
, substComp
, bindComp
, bindsComp
, fromValue
, unBind
, unBind'
, unLam
, Clause(..)
, instantiateClause
, Binding(..)
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
  -- ** Substitution
, subst
, bind
, binds
, Subst
, emptySubst
, insertSubst
, apply
, applyComp
, generalize
, generalizeComp
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

-- FIXME: thunk.
-- FIXME: force.
data Value
  = KType
  | KInterface
  | TSusp Comp
  | ELam Pl [Clause]
  -- | Neutral terms are an unreduced head followed by a stack of eliminators.
  | VNe (Var :$ (Pl, Value))
  | ECon (Q Name :$ Expr)
  | TString
  | EString Text
  -- | Effect operation and its parameters.
  | EOp (Q Name :$ (Pl, Expr))
  -- | Diffs (arising from unification errors).
  | VDiff Value Value

type Type = Value
type Expr = Value


-- | A computation type, represented as a (possibly polymorphic) telescope with signatures on every argument and return.
data Comp
  = TForAll Binding (Type -> Comp)
  | TRet (Maybe [Value]) Type

substCompWith :: (Var -> Value) -> Comp -> Comp
substCompWith f = go
  where
  go = \case
    TForAll t b -> TForAll (binding t) (go . b)
    TRet s t    -> TRet (map (substWith f) <$> s) (substWith f t)

  binding (Binding p n s t) = Binding p n (map (substWith f) <$> s) (substWith f t)

substComp :: IntMap.IntMap Value -> Comp -> Comp
substComp s
  | IntMap.null s = id
  | otherwise     = substCompWith (substMeta s)

bindComp :: Level -> Value -> Comp -> Comp
bindComp k v = bindsComp (IntMap.singleton (getLevel k) v)

bindsComp :: IntMap.IntMap Value -> Comp -> Comp
bindsComp s
  | IntMap.null s = id
  | otherwise     = substCompWith (substFree s)


fromValue :: Value -> Comp
fromValue = \case
  TSusp t -> t
  t       -> TRet mempty t


unBind :: Alternative m => Comp -> m (Binding, Value -> Comp)
unBind = \case{ TForAll t b -> pure (t, b) ; _ -> empty }

-- | A variation on 'unBind' which can be conveniently chained with 'splitr' to strip a prefix of quantifiers off their eventual body.
unBind' :: Alternative m => (Level, Comp) -> m (Binding, (Level, Comp))
unBind' (d, v) = fmap (\ _B -> (succ d, _B (free d))) <$> unBind v


unLam :: Alternative m => Value -> m (Pl, [Clause])
unLam = \case{ ELam n b -> pure (n, b) ; _ -> empty }


data Clause = Clause
  { pattern :: Pattern (Name ::: Type)
  , branch  :: Pattern Value -> Value
  }

instantiateClause :: Level -> Clause -> (Level, Value)
instantiateClause d (Clause p b) = b <$> bindPattern d p


data Binding = Binding
  { pl    :: Pl
  , name  :: Maybe Name
  , delta :: Maybe [Value]
  , type' :: Type
  }


-- Variables

data Var
  = Global (Q Name) -- ^ Global variables, considered equal by 'QName'.
  | Free Level
  | Metavar Meta -- ^ Metavariables, considered equal by 'Level'.

instance Eq Var where
  (==) = curry $ \case
    (Global  q1, Global  q2) -> q1 == q2
    (Global  _,  _)          -> False
    (Free    l1, Free    l2) -> l1 == l2
    (Free    _,  _)          -> False
    (Metavar m1, Metavar m2) -> m1 == m2
    (Metavar _,  _)          -> False

instance Ord Var where
  compare = curry $ \case
    (Global  q1, Global  q2) -> q1 `compare` q2
    (Global  _,  _)          -> LT
    (Free    l1, Free    l2) -> l1 `compare` l2
    (Free    _,  _)          -> LT
    (Metavar m1, Metavar m2) -> m1 `compare` m2
    (Metavar _,  _)          -> LT

unVar :: (Q Name -> a) -> (Level -> a) -> (Meta -> a) -> Var -> a
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


var :: Var -> Value
var = VNe . (:$ Nil)


occursIn :: Meta -> Value -> Bool
occursIn m = go (Level 0) -- FIXME: this should probably be doing something more sensible
  where
  go d = \case
    KType          -> False
    KInterface     -> False
    TSusp c        -> comp d c
    ELam _ cs      -> any (clause d) cs
    VNe (h :$ sp)  -> unVar (const False) (const False) (== m) h || any (any (go d)) sp
    ECon (_ :$ sp) -> any (go d) sp
    TString        -> False
    EString _      -> False
    EOp (_ :$ sp)  -> any (any (go d)) sp
    VDiff v1 v2    -> go d v1 || go d v2

  comp d = \case
    TForAll t b -> binding d t || comp (succ d) (b (free d))
    TRet s t    -> any (any (go d)) s || go d t
  binding d (Binding _ _ s t) = any (any (go d)) s || go d t
  clause d (Clause p b) = any (any (go d)) p || let (d', p') = fill (\ d -> (succ d, free d)) d p in go d' (b p')


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

substWith :: (Var -> Value) -> Value -> Value
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
    VDiff v1 v2   -> VDiff (go v1) (go v2)

  clause (Clause p b) = Clause (fmap go <$> p) (go . b)

-- | Substitute metavars.
subst :: IntMap.IntMap Value -> Value -> Value
subst s
  | IntMap.null s = id
  | otherwise     = substWith (substMeta s)

-- | TForAll a free variable.
bind :: Level -> Value -> Value -> Value
bind k v = binds (IntMap.singleton (getLevel k) v)

binds :: IntMap.IntMap Value -> Value -> Value
binds s
  | IntMap.null s = id
  | otherwise     = substWith (substFree s)

substFree :: IntMap.IntMap Value -> Var -> Value
substFree s = unVar global (\ v -> fromMaybe (free v) (IntMap.lookup (getLevel v) s)) metavar

substMeta :: IntMap.IntMap Value -> Var -> Value
substMeta s = unVar global free (\ m -> fromMaybe (metavar m) (IntMap.lookup (getMeta m) s))


type Subst = IntMap.IntMap (Maybe Value ::: Type)

emptySubst :: Subst
emptySubst = IntMap.empty

insertSubst :: Meta -> Maybe Value ::: Type -> Subst -> Subst
insertSubst n (v ::: _T) = IntMap.insert (getMeta n) (v ::: _T)

-- | Apply the substitution to the value.
apply :: Subst -> Expr -> Value
apply = subst . IntMap.mapMaybe tm -- FIXME: error if the substitution has holes.

applyComp :: Subst -> Comp -> Comp
applyComp = substComp . IntMap.mapMaybe tm -- FIXME: error if the substitution has holes.


-- FIXME: generalize terms and types simultaneously
generalize :: Subst -> Value -> Value
generalize s v
  | null b    = apply s v
  | otherwise = TSusp (foldr (\ (d, _T) b -> TForAll (Binding Im (Just __) Nothing _T) (\ v -> bindComp d v b)) (TRet Nothing (subst (IntMap.mapMaybe tm s <> s') v)) b)
  where
  (s', b, _) = IntMap.foldlWithKey' (\ (s, b, d) m (v ::: _T) -> case v of
    Nothing -> (IntMap.insert m (free d) s, b :> (d, _T), succ d)
    Just _v -> (s, b, d)) (mempty, Nil, Level 0) s

generalizeComp :: Subst -> Comp -> Comp
generalizeComp s v
  | null b    = applyComp s v
  | otherwise = foldr (\ (d, _T) b -> TForAll (Binding Im (Just __) Nothing _T) (\ v -> bindComp d v b)) (substComp (IntMap.mapMaybe tm s <> s') v) b
  where
  (s', b, _) = IntMap.foldlWithKey' (\ (s, b, d) m (v ::: _T) -> case v of
    Nothing -> (IntMap.insert m (free d) s, b :> (d, _T), succ d)
    Just _v -> (s, b, d)) (mempty, Nil, Level 0) s


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
  VNe (h :$ sp) -> minimum (unVar (const SType) ((ctx !) . getIndex . levelToIndex (Level (length ctx))) (const SType) h : toList (sortOf ctx . snd <$> sp))
  ECon _        -> STerm
  TString       -> SType
  EString _     -> STerm
  EOp _         -> STerm -- FIXME: will this always be true?
  VDiff t1 t2   -> sortOf ctx t1 `min` sortOf ctx t2

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
