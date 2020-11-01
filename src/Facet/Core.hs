module Facet.Core
( -- * Values
  Value(..)
, Type
, Expr
, unForAll
, unForAll'
, Clause(..)
, instantiateClause
, Binding(..)
, Var(..)
, unVar
, global
, free
, metavar
, unLam
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
, lookupE
, lookupD
, Import(..)
, Decl(..)
, Def(..)
, unDData
, unDInterface
, matchWith
) where

import           Control.Effect.Empty
import           Control.Lens (Lens', lens)
import           Data.Foldable (foldl', toList)
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.Monoid (First(..))
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
  | TSusp Type
  | TForAll Binding (Type -> Type)
  | ELam Pl [Clause]
  -- | Neutral terms are an unreduced head followed by a stack of eliminators.
  | VNe (Var :$ (Pl, Value))
  | TRet [Value] Type
  | ECon (QName :$ Expr)
  | TString
  | EString Text
  -- | Effect operation and its parameters.
  | EOp (QName :$ (Pl, Expr))

type Type = Value
type Expr = Value


unForAll :: Has Empty sig m => Type -> m (Binding, Value -> Type)
unForAll = \case{ TForAll t b -> pure (t, b) ; _ -> empty }

-- | A variation on 'unBind' which can be conveniently chained with 'splitr' to strip a prefix of quantifiers off their eventual body.
unForAll' :: Has Empty sig m => (Level, Type) -> m (Binding, (Level, Type))
unForAll' (d, v) = fmap (\ _B -> (succ d, _B (free d))) <$> unForAll v


data Clause = Clause
  { pattern :: Pattern (Name ::: Type)
  , branch  :: Pattern Value -> Value
  }

instantiateClause :: Level -> Clause -> (Level, Value)
instantiateClause d (Clause p b) = b <$> bindPattern d p


data Binding = Binding
  { pl    :: Pl
  , name  :: Maybe Name
  , type' :: Type
  }


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


global :: QName -> Value
global = var . Global

free :: Level -> Value
free = var . Free

metavar :: Meta -> Value
metavar = var . Metavar


var :: Var -> Value
var = VNe . (:$ Nil)


unLam :: Has Empty sig m => Value -> m (Pl, [Clause])
unLam = \case{ ELam n b -> pure (n, b) ; _ -> empty }


-- Elimination

($$) :: HasCallStack => Value -> (Pl, Value) -> Value
VNe (h :$ es) $$ a = VNe (h :$ (es :> a))
EOp (q :$ es) $$ a = EOp (q :$ (es :> a))
TForAll _ b   $$ a = b (snd a)
ELam _ b      $$ a = case' (snd a) b
_             $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (HasCallStack, Foldable t) => Value -> t (Pl, Value) -> Value
($$*) = foldl' ($$)

infixl 9 $$, $$*


case' :: HasCallStack => Value -> [Clause] -> Value
case' s cs = case matchWith (\ (Clause p f) -> f <$> match s p) cs of
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
    TSusp t       -> TSusp (go t)
    TForAll t b   -> TForAll (binding t) (go . b)
    TRet s t      -> TRet (map go s) (go t)
    ELam p b      -> ELam p (map clause b)
    VNe (v :$ a)  -> f v $$* fmap (fmap go) a
    ECon c        -> ECon (fmap go c)
    TString       -> TString
    EString s     -> EString s
    EOp (q :$ sp) -> EOp (q :$ fmap (fmap go) sp)

  clause (Clause p b) = Clause p (go . b)
  binding (Binding p n t) = Binding p n (go t)

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


-- FIXME: generalize terms and types simultaneously
generalize :: Subst -> Value -> Value
generalize s v
  | null b    = apply s v
  | otherwise = foldr (\ (d, _T) b -> TForAll (Binding Im (Just __) _T) (\ v -> bind d v b)) (subst (IntMap.mapMaybe tm s <> s') v) b
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
  KType                       -> SKind
  KInterface                  -> SKind
  TSusp _                     -> SType
  TForAll (Binding _ _ _T) _B -> let _T' = sortOf ctx _T in min _T' (sortOf (ctx :> _T') (_B (free (Level (length ctx)))))
  TRet _ _T                   -> sortOf ctx _T
  ELam{}                      -> STerm
  VNe (h :$ sp)               -> minimum (unVar (const SType) ((ctx !) . getIndex . levelToIndex (Level (length ctx))) (const SType) h : toList (sortOf ctx . snd <$> sp))
  ECon _                      -> STerm
  TString                     -> SType
  EString _                   -> STerm
  EOp _                       -> STerm -- FIXME: will this always be true?


-- Patterns

data Pattern a
  = PVar a
  | PCon (QName :$ Pattern a)
  | PEff QName (Stack (Pattern a)) a
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
  , decls     :: Map.Map Name Decl
  }

name_ :: Lens' Module MName
name_ = lens (\ Module{ name } -> name) (\ m name -> (m :: Module){ name })

imports_ :: Lens' Module [Import]
imports_ = lens imports (\ m imports -> m{ imports })

decls_ :: Lens' Module (Map.Map Name Decl)
decls_ = lens decls (\ m decls -> m{ decls })


-- FIXME: produce multiple results, if they exist.
lookupC :: Has Empty sig m => Name -> Module -> m (QName :=: Maybe Def ::: Type)
lookupC n Module{ name, decls } = maybe empty pure $ matchWith matchDef (toList decls)
  where
  -- FIXME: insert the constructors into the top-level scope instead of looking them up under the datatype.
  matchDef (Decl   d     _)  = maybe empty pure d >>= unDData >>= matchWith matchCon
  matchCon (n' :=: v ::: _T) = (name :.: n' :=: Just (DTerm v) ::: _T) <$ guard (n == n')

-- | Look up effect operations.
lookupE :: Has Empty sig m => Name -> Module -> m (QName :=: Maybe Def ::: Type)
-- FIXME: produce multiple results, if they exist.
lookupE n Module{ name, decls } = maybe empty pure $ matchWith matchDef (toList decls)
  where
  -- FIXME: insert the constructors into the top-level scope instead of looking them up under the datatype.
  matchDef (Decl   d     _)  = maybe empty pure d >>= unDInterface >>= matchWith matchCon
  matchCon (n' ::: _T) = (name :.: n' :=: Nothing ::: _T) <$ guard (n == n')

-- FIXME: produce multiple results, if they exist.
lookupD :: Has Empty sig m => Name -> Module -> m (QName :=: Maybe Def ::: Type)
lookupD n Module{ name = mname, decls } = maybe empty pure $ do
  Decl d _T <- Map.lookup n decls
  pure $ mname :.: n :=: d ::: _T


newtype Import = Import { name :: MName }

-- FIXME: keep track of free variables in declarations so we can work incrementally
data Decl = Decl
  { def   :: Maybe Def
  , type' :: Type
  }

-- FIXME: submodules
data Def
  = DTerm Value
  -- FIXME: this should be a module.
  | DData [Name :=: Value ::: Type]
  -- FIXME: this should be a module.
  | DInterface [Name ::: Type]

unDData :: Has Empty sig m => Def -> m [Name :=: Value ::: Type]
unDData = \case
  DData cs -> pure cs
  _        -> empty

unDInterface :: Has Empty sig m => Def -> m [Name ::: Type]
unDInterface = \case
  DInterface cs -> pure cs
  _             -> empty


matchWith :: Foldable t => (a -> Maybe b) -> t a -> Maybe b
matchWith rel = getFirst . foldMap (First . rel)
