module Facet.Core
( -- * Values
  Value(..)
, compareValue
, compareBinding
, compareClause
, compareSig
, compareDelta
, Telescope(..)
, compareTelescope
, substTelescope
, bindTelescope
, bindsTelescope
, fromValue
, unBind
, unBind'
, Clause(..)
, instantiateClause
, Binding(..)
, Delta(..)
, Sig(..)
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
, mvs
, generalize
  -- ** Classification
, Sort(..)
, sortOf
  -- * Patterns
, Pattern(..)
, fill
, bindPattern
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
import qualified Data.Set as Set
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
  | VComp Telescope
  | VLam Pl [Clause]
  -- | Neutral terms are an unreduced head followed by a stack of eliminators.
  | VNeut Var (Stack (Pl, Value))
  | VCon (Con Value)

instance Eq Value where
  a == b = compareValue 0 a b == EQ

instance Ord Value where
  compare = compareValue 0

compareValue :: Level -> Value -> Value -> Ordering
compareValue d = curry $ \case
  -- defined thus instead of w/ fallback case to have exhaustiveness checks kick in when adding constructors.
  (VType, VType)               -> EQ
  (VType, _)                   -> LT
  (VInterface, VInterface)     -> EQ
  (VInterface, _)              -> LT
  (VComp t1, VComp t2)         -> compareTelescope d t1 t2
  (VComp{}, _)                 -> LT
   -- FIXME: do we need to test the types here?
  (VLam p1 cs1, VLam p2 cs2)   -> compare p1 p2 <> liftCompare (compareClause d) cs1 cs2
  (VLam{}, _)                  -> LT
  (VNeut h1 sp1, VNeut h2 sp2) -> compareVar d h1 h2 <> liftCompare (liftCompare (compareValue d)) sp1 sp2
  (VNeut{}, _)                 -> LT
  (VCon c1, VCon c2)           -> liftCompare (compareValue d) c1 c2
  (VCon _, _)                  -> LT

compareVar :: Level -> Var -> Var -> Ordering
compareVar d = curry $ \case
  (Global (q1 ::: t1), Global (q2 ::: t2))   -> compare q1 q2 <> compareTelescope d t1 t2
  (Global _, _)                              -> LT
  (Free d1, Free d2)                         -> compare d1 d2
  (Free _, _)                                -> LT
  (Metavar (m1 ::: t1), Metavar (m2 ::: t2)) -> compare m1 m2 <> compareValue d t1 t2
  (Metavar _, _)                             -> LT

compareBinding :: Level -> Binding -> Binding -> Ordering
compareBinding d (Binding p1 _ s1) (Binding p2 _ s2) = compare p1 p2 <> compareSig d s1 s2

compareClause :: Level -> Clause -> Clause -> Ordering
compareClause d (Clause p1 b1) (Clause p2 b2) = liftCompare (\ _ _ -> EQ) p1 p2 <> compareValue d' (b1 p') (b2 p')
  where
  (d', p') = bindPattern d p1

compareSig :: Level -> Sig -> Sig -> Ordering
compareSig d (Sig s1 t1) (Sig s2 t2) = liftCompare (compareDelta d) s1 s2 <> compareValue d t1 t2

compareDelta :: Level -> Delta -> Delta -> Ordering
compareDelta d (Delta (q1 ::: _) sp1) (Delta (q2 ::: _) sp2) = compare q1 q2 <> liftCompare (compareValue d) sp1 sp2


-- | A telescope represents a (possibly polymorphic) computation type.
data Telescope
  = Bind Binding (Value -> Telescope)
  | End Sig

compareTelescope :: Level -> Telescope -> Telescope -> Ordering
compareTelescope d = curry $ \case
  (Bind t1 b1, Bind t2 b2) -> compareBinding d t1 t2 <> compareTelescope (succ d) (b1 (free d)) (b2 (free d))
  (Bind{}, _)              -> LT
  (End s1, End s2)         -> compareSig d s1 s2
  (End{}, _)               -> LT

substTelescope :: IntMap.IntMap Value -> Telescope -> Telescope
substTelescope s
  | IntMap.null s = id
  | otherwise     = go
  where
  go = \case
    Bind t b -> Bind (binding t) (go . b)
    End s    -> End (sig s)

  binding (Binding p n s) = Binding p n (sig s)

  sig (Sig d t) = Sig (Set.map delta d) (subst s t)
  delta (Delta (q ::: t) sp) = Delta (q ::: subst s t) (fmap (subst s) sp)


bindTelescope :: HasCallStack => Level -> Value -> Telescope -> Telescope
bindTelescope k v = bindsTelescope (IntMap.singleton (getLevel k) v)

bindsTelescope :: HasCallStack => IntMap.IntMap Value -> Telescope -> Telescope
bindsTelescope subst = go
  where
  go = \case
    Bind t b -> Bind (binding t) (go . b)
    End s    -> End (sig s)

  binding (Binding p n s) = Binding p n (sig s)
  sig (Sig d t) = Sig (Set.map delta d) (binds subst t)
  delta (Delta (q ::: t) sp) = Delta (q ::: binds subst t) (fmap (binds subst) sp)


fromValue :: Value -> Telescope
fromValue = \case
  VComp t -> t
  t       -> End (Sig mempty t)


unBind :: Has Empty sig m => Telescope -> m (Binding, Value -> Telescope)
unBind = \case{ Bind t b -> pure (t, b) ; _ -> empty }

-- | A variation on 'unBind' which can be conveniently chained with 'splitr' to strip a prefix of quantifiers off their eventual body.
unBind' :: Has Empty sig m => (Level, Telescope) -> m (Binding, (Level, Telescope))
unBind' (d, v) = fmap (\ _B -> (succ d, _B (free d))) <$> unBind v


data Clause = Clause
  { pattern :: Pattern (UName ::: Value)
  , branch  :: Pattern Value -> Value
  }

instantiateClause :: Level -> Clause -> (Level, Value)
instantiateClause d (Clause p b) = b <$> bindPattern d p


data Binding = Binding
  { _pl  :: Pl
  , name :: UName
  , sig  :: Sig
  }


data Delta = Delta (QName ::: Value) (Stack Value)

instance Eq Delta where
  Delta (q1 ::: _) as1 == Delta (q2 ::: _) as2 = q1 == q2 && as1 == as2

instance Ord Delta where
  Delta (q1 ::: _) as1 `compare` Delta (q2 ::: _) as2 = q1 `compare` q2 <> as1 `compare` as2


data Sig = Sig
  { delta :: Set.Set Delta
  , type' :: Value
  }


data Var
  = Global (QName ::: Telescope) -- ^ Global variables, considered equal by 'QName'.
  | Free Level
  | Metavar (Meta ::: Value) -- ^ Metavariables, considered equal by 'Level'.

instance Eq Var where
  (==) = curry $ \case
    (Global  (q1 ::: _), Global  (q2 ::: _)) -> q1 == q2
    (Global  _,          _)                  -> False
    (Free    l1,         Free    l2)         -> l1 == l2
    (Free    _,          _)                  -> False
    (Metavar (m1 ::: _), Metavar (m2 ::: _)) -> m1 == m2
    (Metavar _,          _)                  -> False

instance Ord Var where
  compare = curry $ \case
    (Global  (q1 ::: _), Global  (q2 ::: _)) -> q1 `compare` q2
    (Global  _,          _)                  -> LT
    (Free    l1,         Free    l2)         -> l1 `compare` l2
    (Free    _,          _)                  -> LT
    (Metavar (m1 ::: _), Metavar (m2 ::: _)) -> m1 `compare` m2
    (Metavar _,          _)                  -> LT


unVar :: (QName ::: Telescope -> a) -> (Level -> a) -> (Meta ::: Value -> a) -> Var -> a
unVar f g h = \case
  Global  n -> f n
  Free    n -> g n
  Metavar n -> h n


data Con a = Con (QName ::: Telescope) (Stack a)
  deriving (Foldable, Functor, Traversable)

instance Eq a => Eq (Con a) where
  (==) = eq1

instance Ord a => Ord (Con a) where
  compare = compare1

instance Eq1 Con where
  liftEq eq (Con (q1 ::: _) sp1) (Con (q2 ::: _) sp2) = q1 == q2 && liftEq eq sp1 sp2

instance Ord1 Con where
  liftCompare compare' (Con (q1 ::: _) sp1) (Con (q2 ::: _) sp2) = compare q1 q2 <> liftCompare compare' sp1 sp2


global :: QName ::: Telescope -> Value
global = var . Global

free :: Level -> Value
free = var . Free

metavar :: Meta ::: Value -> Value
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
    t@Bind{}      -> VComp t
    End (Sig _ t) -> t
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
    guard (tm n == tm n')
    -- NB: we’re assuming they’re the same length because they’ve passed elaboration.
    PCon . Con n' <$> sequenceA (zipWith match fs ps)
  (_,                PCon _)          -> Nothing


-- | Substitute metavars.
subst :: HasCallStack => IntMap.IntMap Value -> Value -> Value
subst s
  | IntMap.null s = id
  | otherwise     = go
  where
  go = \case
    VType       -> VType
    VInterface  -> VInterface
    VComp t   -> VComp (substTelescope s t)
    VLam    p b -> VLam p (map clause b)
    VNeut f a   -> unVar global free (s !) f' $$* fmap (fmap go) a
      where
      f' = case f of
        Global  (n ::: _T) -> Global  (n ::: substTelescope s _T)
        Free    v          -> Free    v
        Metavar (d ::: _T) -> Metavar (d ::: go _T)
    VCon c      -> VCon (fmap go c)

  clause (Clause p b) = Clause p (go . b)

  s ! l = case IntMap.lookup (getMeta (tm l)) s of
    Just a  -> a
    Nothing -> metavar l

-- | Bind a free variable.
bind :: HasCallStack => Level -> Value -> Value -> Value
bind k v = binds (IntMap.singleton (getLevel k) v)

binds :: HasCallStack => IntMap.IntMap Value -> Value -> Value
binds subst = go
  where
  go = \case
    VType      -> VType
    VInterface -> VInterface
    VComp t    -> VComp (bindsTelescope subst t)
    VLam  p b  -> VLam p (map clause b)
    VNeut f a  -> unVar global (\ v -> fromMaybe (free v) (IntMap.lookup (getLevel v) subst)) metavar f' $$* fmap (fmap go) a
      where
      f' = case f of
        Global  (n ::: _T) -> Global  (n ::: bindsTelescope subst _T)
        Free    v          -> Free    v
        Metavar (d ::: _T) -> Metavar (d ::: go _T)
    VCon c     -> VCon (fmap go c)

  clause (Clause p b) = Clause p (go . b)


mvs :: Level -> Value -> IntMap.IntMap Value
mvs d = \case
  VType                   -> mempty
  VInterface              -> mempty
  VComp t                 -> telescope d t
  VLam _ cs               -> foldMap clause cs
  VNeut h sp              -> unVar (telescope d . ty) mempty (\ (m ::: _T) -> IntMap.insert (getMeta m) _T (mvs d _T)) h <> foldMap (foldMap (mvs d)) sp
  VCon (Con (_ ::: t) fs) -> telescope d t <> foldMap (mvs d) fs
  where
  telescope d = \case
    Bind t b -> binding d t <> telescope (succ d) (b (free d))
    End s    -> sig d s
  binding d (Binding _ _ s) = sig d s
  clause (Clause p b) = let (d', p') = bindPattern d p in mvs d' (b p')
  sig d (Sig s t) = foldMap (delta d) s <> mvs d t
  delta d (Delta (_ ::: t) sp) = mvs d t <> foldMap (mvs d) sp


-- FIXME: this seems to break multiple binders, e.g. pair:
-- pair {?A} {?B} : { _A : Type } -> { _B : Type } -> _A -> _A -> Pair _A _A
-- (vs. non-generalized: pair {?A} {?B} : ?A -> ?B -> Pair ?A ?B)
-- FIXME: this doesn’t generalize type applications apparently
generalize :: Value -> Value
generalize v = VComp (build (End (Sig mempty (subst s v))))
  where
  metas = mvs 0 v
  (_, build, s) = IntMap.foldrWithKey (\ m _T (d, f, s) -> (succ d, \ b -> Bind (Binding Im __ (Sig mempty _T)) (\ v -> bindTelescope d v (f b)), IntMap.insert m (free d) s)) (0, id, IntMap.empty) metas


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
  VNeut h sp -> minimum (unVar (pred . telescope ctx . ty) ((ctx !) . getIndex . levelToIndex (Level (length ctx))) (pred . sortOf ctx . ty) h : toList (sortOf ctx . snd <$> sp))
  VCon _     -> STerm
  where
  telescope ctx = \case
    Bind (Binding _ _ _T) _B -> let _T' = sig ctx _T in min _T' (telescope (ctx :> _T') (_B (free (Level (length ctx)))))
    End s                    -> sig ctx s
  sig ctx (Sig _ _T) = sortOf ctx _T


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
lookupC :: Has Empty sig m => UName -> Module -> m (QName :=: Maybe Def ::: Telescope)
lookupC n Module{ name, decls } = maybe empty pure $ matchWith matchDef (toList decls)
  where
  -- FIXME: insert the constructors into the top-level scope instead of looking them up under the datatype.
  matchDef (Decl   d     _)  = maybe empty pure d >>= unDData >>= matchWith matchCon
  matchCon (n' :=: v ::: _T) = (name :.: C n' :=: Just (DTerm v) ::: _T) <$ guard (n == n')

-- FIXME: produce multiple results, if they exist.
lookupD :: Has Empty sig m => DName -> Module -> m (QName :=: Maybe Def ::: Telescope)
lookupD n Module{ name = mname, decls } = maybe empty pure $ do
  Decl d _T <- Map.lookup n decls
  pure $ mname :.: n :=: d ::: _T


newtype Import = Import { name :: MName }

-- FIXME: keep track of free variables in declarations so we can work incrementally
data Decl = Decl
  { def   :: Maybe Def
  , type' :: Telescope
  }

data Def
  = DTerm Value
  | DData [UName :=: Value ::: Telescope]
  | DInterface [UName ::: Telescope]

unDData :: Has Empty sig m => Def -> m [UName :=: Value ::: Telescope]
unDData = \case
  DData cs -> pure cs
  _        -> empty

unDInterface :: Has Empty sig m => Def -> m [UName ::: Telescope]
unDInterface = \case
  DInterface cs -> pure cs
  _             -> empty


matchWith :: Foldable t => (a -> Maybe b) -> t a -> Maybe b
matchWith rel = getFirst . foldMap (First . rel)
