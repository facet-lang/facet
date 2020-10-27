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
, Clause(..)
, instantiateClause
, Binding(..)
, Interface(..)
, Var(..)
, Con(..)
, unVar
, global
, free
, metavar
, unLam
, ($$)
, ($$*)
, case'
, match
, subst
, bind
, binds
, Subst
, emptySubst
, insertSubst
, apply
, applyComp
, generalize
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
, decls_
, lookupC
, lookupD
, Import(..)
, Decl(..)
, Def(..)
, unDData
, unDInterface
) where

import           Control.Effect.Empty
import           Control.Lens (Lens', lens)
import           Data.Foldable (foldl', toList)
import           Data.Functor.Classes
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.Monoid (First(..))
import           Data.Semialign
import           Data.Traversable (mapAccumL)
import           Facet.Name hiding (bind)
import           Facet.Stack
import           Facet.Syntax
import           GHC.Stack
import           Prelude hiding (zip, zipWith)

-- Values

data Value
  = VType
  | VInterface
  | VComp Comp
  | VLam Pl [Clause]
  -- | Neutral terms are an unreduced head followed by a stack of eliminators.
  | VNeut Var (Stack (Pl, Value))
  | VCon (Con Value)

type Type = Value
type Expr = Value


-- | A computation type, represented as a (possibly polymorphic) telescope with signatures on every argument and return.
data Comp
  = Bind Binding (Type -> Comp)
  | Comp [Interface] Type

substCompWith :: (Var -> Value) -> Comp -> Comp
substCompWith f = go
  where
  go = \case
    Bind t b -> Bind (binding t) (go . b)
    Comp s t -> Comp s (substWith f t)

  binding (Binding p n d t) = Binding p n (map interface d) (substWith f t)

  interface (Interface q sp) = Interface q (fmap (substWith f) sp)

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
  VComp t -> t
  t       -> Comp mempty t


unBind :: Has Empty sig m => Comp -> m (Binding, Value -> Comp)
unBind = \case{ Bind t b -> pure (t, b) ; _ -> empty }

-- | A variation on 'unBind' which can be conveniently chained with 'splitr' to strip a prefix of quantifiers off their eventual body.
unBind' :: Has Empty sig m => (Level, Comp) -> m (Binding, (Level, Comp))
unBind' (d, v) = fmap (\ _B -> (succ d, _B (free d))) <$> unBind v


data Clause = Clause
  { pattern :: Pattern (UName ::: Value)
  , branch  :: Pattern Value -> Value
  }

instantiateClause :: Level -> Clause -> (Level, Value)
instantiateClause d (Clause p b) = b <$> bindPattern d p


data Binding = Binding
  { pl    :: Pl
  , name  :: UName
  , delta :: [Interface]
  , type' :: Value
  }


data Interface = Interface QName (Stack Value)


data Var
  = Global QName -- ^ Global variables, considered equal by 'QName'.
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

unVar :: (QName -> a) -> (Level -> a) -> (Meta -> a) -> Var -> a
unVar f g h = \case
  Global  n -> f n
  Free    n -> g n
  Metavar n -> h n


data Con a = Con QName (Stack a)
  deriving (Foldable, Functor, Traversable)

instance Eq a => Eq (Con a) where
  (==) = eq1

instance Ord a => Ord (Con a) where
  compare = compare1

instance Eq1 Con where
  liftEq eq (Con q1 sp1) (Con q2 sp2) = q1 == q2 && liftEq eq sp1 sp2

instance Ord1 Con where
  liftCompare compare' (Con q1 sp1) (Con q2 sp2) = compare q1 q2 <> liftCompare compare' sp1 sp2


global :: QName -> Value
global = var . Global

free :: Level -> Value
free = var . Free

metavar :: Meta -> Value
metavar = var . Metavar


var :: Var -> Value
var = (`VNeut` Nil)


unLam :: Has Empty sig m => Value -> m (Pl, [Clause])
unLam = \case{ VLam n b -> pure (n, b) ; _ -> empty }


-- FIXME: how should this work in weak/parametric HOAS?
($$) :: HasCallStack => Value -> (Pl, Value) -> Value
VNeut h es $$ a = VNeut h (es :> a)
VComp  t $$ a
  | Bind _ b <- t = case b (snd a) of
    t@Bind{} -> VComp t
    Comp _ t -> t
VLam _   b $$ a = case' (snd a) b
_          $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (HasCallStack, Foldable t) => Value -> t (Pl, Value) -> Value
($$*) = foldl' ($$)

infixl 9 $$, $$*


case' :: HasCallStack => Value -> [Clause] -> Value
case' s cs
  | Clause p f:_ <- cs
  , PVar _ <- p       = f (PVar s)
case' s cs = case matchWith (\ (Clause p f) -> f <$> match s p) cs of
  Just v -> v
  _      -> error "non-exhaustive patterns in lambda"

match :: Value -> Pattern b -> Maybe (Pattern Value)
match = curry $ \case
  (s,                PVar _)          -> Just (PVar s)
  (VCon (Con n' fs), PCon (Con n ps)) -> do
    guard (n == n')
    -- NB: we’re assuming they’re the same length because they’ve passed elaboration.
    PCon . Con n' <$> sequenceA (zipWith match fs ps)
  (_,                PCon _)          -> Nothing


substWith :: (Var -> Value) -> Value -> Value
substWith f = go
  where
  go = \case
    VType       -> VType
    VInterface  -> VInterface
    VComp t     -> VComp (substCompWith f t)
    VLam    p b -> VLam p (map clause b)
    VNeut v a   -> f v $$* fmap (fmap go) a
    VCon c      -> VCon (fmap go c)

  clause (Clause p b) = Clause p (go . b)

-- | Substitute metavars.
subst :: IntMap.IntMap Value -> Value -> Value
subst s
  | IntMap.null s = id
  | otherwise     = substWith (substMeta s)

-- | Bind a free variable.
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
apply s v = subst (IntMap.mapMaybe tm s) v -- FIXME: error if the substitution has holes.

applyComp :: Subst -> Comp -> Comp
applyComp s v = substComp (IntMap.mapMaybe tm s) v -- FIXME: error if the substitution has holes.


generalize :: Subst -> Value -> Value
generalize s v = VComp (foldr (\ (d, _T) b -> Bind (Binding Im __ mempty _T) (\ v -> bindComp d v b)) (Comp mempty (subst (IntMap.mapMaybe tm s <> s') v)) b)
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
  VType      -> SKind
  VInterface -> SKind
  VComp t    -> telescope ctx t
  VLam{}     -> STerm
  VNeut h sp -> minimum (unVar (const SType) ((ctx !) . getIndex . levelToIndex (Level (length ctx))) (const SType) h : toList (sortOf ctx . snd <$> sp))
  VCon _     -> STerm
  where
  telescope ctx = \case
    Bind (Binding _ _ _ _T) _B -> let _T' = sortOf ctx _T in min _T' (telescope (ctx :> _T') (_B (free (Level (length ctx)))))
    Comp _ _T                  -> sortOf ctx _T


-- Patterns

data Pattern a
  = PVar a
  | PCon (Con (Pattern a))
  deriving (Eq, Foldable, Functor, Ord, Traversable)

instance Eq1 Pattern where
  liftEq eq (PVar v1) (PVar v2) = eq v1 v2
  liftEq _  PVar{}    _         = False
  liftEq eq (PCon c1) (PCon c2) = liftEq (liftEq eq) c1 c2
  liftEq _  PCon{}    _         = False

instance Ord1 Pattern where
  liftCompare compare' (PVar v1) (PVar v2) = compare' v1 v2
  liftCompare _        PVar{}    _         = LT
  liftCompare compare' (PCon c1) (PCon c2) = liftCompare (liftCompare compare') c1 c2
  liftCompare _        PCon{}    _         = LT

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
  , decls     :: Map.Map DName Decl
  }

name_ :: Lens' Module MName
name_ = lens (\ Module{ name } -> name) (\ m name -> (m :: Module){ name })

imports_ :: Lens' Module [Import]
imports_ = lens imports (\ m imports -> m{ imports })

decls_ :: Lens' Module (Map.Map DName Decl)
decls_ = lens decls (\ m decls -> m{ decls })


-- FIXME: produce multiple results, if they exist.
lookupC :: Has Empty sig m => UName -> Module -> m (QName :=: Maybe Def ::: Comp)
lookupC n Module{ name, decls } = maybe empty pure $ matchWith matchDef (toList decls)
  where
  -- FIXME: insert the constructors into the top-level scope instead of looking them up under the datatype.
  matchDef (Decl   d     _)  = maybe empty pure d >>= unDData >>= matchWith matchCon
  matchCon (n' :=: v ::: _T) = (name :.: C n' :=: Just (DTerm v) ::: _T) <$ guard (n == n')

-- FIXME: produce multiple results, if they exist.
lookupD :: Has Empty sig m => DName -> Module -> m (QName :=: Maybe Def ::: Comp)
lookupD n Module{ name = mname, decls } = maybe empty pure $ do
  Decl d _T <- Map.lookup n decls
  pure $ mname :.: n :=: d ::: _T


newtype Import = Import { name :: MName }

-- FIXME: keep track of free variables in declarations so we can work incrementally
data Decl = Decl
  { def   :: Maybe Def
  , type' :: Comp
  }

data Def
  = DTerm Value
  | DData [UName :=: Value ::: Comp]
  | DInterface [UName ::: Comp]

unDData :: Has Empty sig m => Def -> m [UName :=: Value ::: Comp]
unDData = \case
  DData cs -> pure cs
  _        -> empty

unDInterface :: Has Empty sig m => Def -> m [UName ::: Comp]
unDInterface = \case
  DInterface cs -> pure cs
  _             -> empty


matchWith :: Foldable t => (a -> Maybe b) -> t a -> Maybe b
matchWith rel = getFirst . foldMap (First . rel)
