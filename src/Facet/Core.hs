module Facet.Core
( -- * Values
  Value(..)
, compareValue
, compareBinding
, compareClause
, compareSig
, compareDelta
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
, unForAll
, unForAll'
, unLam
, ($$)
, ($$*)
, case'
, match
, subst
, bind
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

import           Control.Applicative ((<|>))
import           Control.Effect.Empty
import           Control.Lens (Lens', lens)
import           Data.Foldable (find, foldl', toList)
import           Data.Functor.Classes
import qualified Data.IntMap as IntMap
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
  | VForAll Binding (Value -> Value)
  | VLam Pl [Clause]
  -- | Neutral terms are an unreduced head followed by a stack of eliminators.
  | VNeut (Var Value) (Stack (Pl_ Value))
  | VCon (Con Value)

instance Eq Value where
  a == b = compareValue 0 a b == EQ

instance Ord Value where
  compare = compareValue 0

compareValue :: Level -> Value -> Value -> Ordering
compareValue d = curry $ \case
  -- defined thus instead of w/ fallback case to have exhaustiveness checks kick in when adding constructors.
  (VType, VType)                 -> EQ
  (VType, _)                     -> LT
  (VInterface, VInterface)       -> EQ
  (VInterface, _)                -> LT
  (VForAll t1 b1, VForAll t2 b2) -> compareBinding d t1 t2 <> compareValue (succ d) (b1 (free d)) (b2 (free d))
  (VForAll{}, _)                 -> LT
   -- FIXME: do we need to test the types here?
  (VLam p1 cs1, VLam p2 cs2)     -> compare p1 p2 <> liftCompare (compareClause d) cs1 cs2
  (VLam{}, _)                    -> LT
  (VNeut h1 sp1, VNeut h2 sp2)   -> compareH d h1 h2 <> liftCompare (liftCompare (compareValue d)) sp1 sp2
  (VNeut{}, _)                   -> LT
  (VCon c1, VCon c2)             -> compareCon compareValue d c1 c2
  (VCon _, _)                    -> LT
  where
  compareH d = curry $ \case
    (Global (q1 ::: t1), Global (q2 ::: t2))   -> compare q1 q2 <> compareValue d t1 t2
    (Global _, _)                              -> LT
    (Free d1, Free d2)                         -> compare d1 d2
    (Free _, _)                                -> LT
    (Metavar (m1 ::: t1), Metavar (m2 ::: t2)) -> compare m1 m2 <> compareValue d t1 t2
    (Metavar _, _)                             -> LT
  compareCon :: (Level -> a -> b -> Ordering) -> Level -> Con a -> Con b -> Ordering
  compareCon compareValue' d (Con (n1 ::: t1) fs1) (Con (n2 ::: t2) fs2) = compare n1 n2 <> compareValue d t1 t2 <> liftCompare (compareValue' d) fs1 fs2

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


data Var t
  = Global (QName ::: t) -- ^ Global variables, considered equal by 'QName'.
  | Free Level
  | Metavar (Meta ::: t) -- ^ Metavariables, considered equal by 'Level'.
  deriving (Foldable, Functor, Show, Traversable)

instance Eq (Var t) where
  Global  (q1 ::: _) == Global  (q2 ::: _) = q1 == q2
  Global  _          == _                  = False
  Free    l1         == Free    l2         = l1 == l2
  Free    _          == _                  = False
  Metavar (m1 ::: _) == Metavar (m2 ::: _) = m1 == m2
  Metavar _          == _                  = False

instance Ord (Var t) where
  Global  (q1 ::: _) `compare` Global  (q2 ::: _) = q1 `compare` q2
  Global  _          `compare` _                  = LT
  Free    l1         `compare` Free    l2         = l1 `compare` l2
  Free    _          `compare` _                  = LT
  Metavar (m1 ::: _) `compare` Metavar (m2 ::: _) = m1 `compare` m2
  Metavar _          `compare` _                  = LT


unVar :: (QName ::: a -> b) -> (Level -> b) -> (Meta ::: a -> b) -> Var a -> b
unVar f g h = \case
  Global  n -> f n
  Free    n -> g n
  Metavar n -> h n


data Con a = Con (QName ::: Value) (Stack a)
  deriving (Eq, Foldable, Functor, Ord, Traversable)

instance Eq1 Con where
  liftEq eq (Con (q1 ::: _) sp1) (Con (q2 ::: _) sp2) = q1 == q2 && liftEq eq sp1 sp2

instance Ord1 Con where
  liftCompare compare' (Con (q1 ::: _) sp1) (Con (q2 ::: _) sp2) = compare q1 q2 <> liftCompare compare' sp1 sp2


global :: QName ::: Value -> Value
global = var . Global

free :: Level -> Value
free = var . Free

metavar :: Meta ::: Value -> Value
metavar = var . Metavar


var :: Var Value -> Value
var = (`VNeut` Nil)


unForAll :: Has Empty sig m => Value -> m (Binding, Value -> Value)
unForAll = \case{ VForAll t b -> pure (t, b) ; _ -> empty }

-- | A variation on 'unForAll' which can be conveniently chained with 'splitr' to strip a prefix of quantifiers off their eventual body.
unForAll' :: Has Empty sig m => (Level, Value) -> m (Binding, (Level, Value))
unForAll' (d, v) = do
  (_T, _B) <- unForAll v
  pure (_T, (succ d, _B (free d)))

unLam :: Has Empty sig m => Value -> m (Pl, [Clause])
unLam = \case{ VLam n b -> pure (n, b) ; _ -> empty }


-- FIXME: how should this work in weak/parametric HOAS?
($$) :: HasCallStack => Value -> (Pl_ Value) -> Value
VNeut h es  $$ a = VNeut h (es :> a)
VForAll _ b $$ a = b (out a)
VLam _    b $$ a = case' (out a) b
_           $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (HasCallStack, Foldable t) => Value -> t (Pl_ Value) -> Value
($$*) = foldl' ($$)

infixl 9 $$, $$*


case' :: HasCallStack => Value -> [Clause] -> Value
case' s            cs
  | Clause p f:_ <- cs
  , PVar _ <- p       = f (PVar s)
case' s            cs = case matchWith (\ (Clause p f) -> f <$> match s p) cs of
  Just v -> v
  _      -> error "non-exhaustive patterns in lambda"

match :: Value -> Pattern b -> Maybe (Pattern Value)
match = curry $ \case
  (s,          PVar _)                -> Just (PVar s)
  (VCon (Con n' fs), PCon (Con n ps)) -> do
    guard (tm n == tm n')
    -- NB: we’re assuming they’re the same length because they’ve passed elaboration.
    PCon . Con n' <$> sequenceA (zipWith match fs ps)
  (_,          PCon _)                -> Nothing


-- | Substitute metavars.
subst :: HasCallStack => IntMap.IntMap Value -> Value -> Value
subst s
  | IntMap.null s = id
  | otherwise     = go
  where
  go = \case
    VType       -> VType
    VInterface  -> VInterface
    VForAll t b -> VForAll (binding t) (go . b)
    VLam    p b -> VLam p (map clause b)
    VNeut f a   -> unVar global free (s !) f' $$* fmap (fmap go) a
      where
      f' = case f of
        Global  (n ::: _T) -> Global  (n ::: go _T)
        Free    v          -> Free    v
        Metavar (d ::: _T) -> Metavar (d ::: go _T)
    VCon c      -> VCon (fmap go c)

  binding (Binding p n s) = Binding p n (sig s)
  clause (Clause p b) = Clause p (go . b)

  sig (Sig d t) = Sig (Set.map delta d) (go t)

  delta (Delta (q ::: t) sp) = Delta (q ::: go t) (fmap go sp)

  s ! l = case IntMap.lookup (getMeta (tm l)) s of
    Just a  -> a
    Nothing -> metavar l

-- | Bind a free variable.
bind :: HasCallStack => Level -> Value -> Value -> Value
bind target with = go
  where
  go = \case
    VType       -> VType
    VInterface  -> VInterface
    VForAll t b -> VForAll (binding t) (go . b)
    VLam    p b -> VLam p (map clause b)
    VNeut f a   -> unVar global (\ v -> if v == target then with else free v) metavar f' $$* fmap (fmap go) a
      where
      f' = case f of
        Global  (n ::: _T) -> Global  (n ::: go _T)
        Free    v          -> Free    v
        Metavar (d ::: _T) -> Metavar (d ::: go _T)
    VCon c      -> VCon (fmap go c)

  binding (Binding p n s) = Binding p n (sig s)
  clause (Clause p b) = Clause p (go . b)

  sig (Sig d t) = Sig (Set.map delta d) (go t)

  delta (Delta (q ::: t) sp) = Delta (q ::: go t) (fmap go sp)


mvs :: Level -> Value -> IntMap.IntMap Value
mvs d = \case
  VType                   -> mempty
  VInterface              -> mempty
  VForAll t b             -> binding d t <> mvs (succ d) (b (free d))
  VLam _ cs               -> foldMap clause cs
  VNeut h sp              -> unVar (mvs d . ty) mempty (\ (m ::: _T) -> IntMap.insert (getMeta m) _T (mvs d _T)) h <> foldMap (foldMap (mvs d)) sp
  VCon (Con (_ ::: t) fs) -> mvs d t <> foldMap (mvs d) fs
  where
  binding d (Binding _ _ s) = sig d s
  clause (Clause p b) = let (d', p') = bindPattern d p in mvs d' (b p')
  sig d (Sig s t) = foldMap (delta d) s <> mvs d t
  delta d (Delta (_ ::: t) sp) = mvs d t <> foldMap (mvs d) sp


-- FIXME: this seems to break multiple binders, e.g. pair:
-- pair {?A} {?B} : { _A : Type } -> { _B : Type } -> _A -> _A -> Pair _A _A
-- (vs. non-generalized: pair {?A} {?B} : ?A -> ?B -> Pair ?A ?B)
-- FIXME: this doesn’t generalize type applications apparently
generalize :: Value -> Value
generalize v = build s v
  where
  metas = mvs 0 v
  (_, build, s) = IntMap.foldrWithKey (\ m _T (d, f, s) -> (succ d, \ s b -> VForAll (Binding Im __ (Sig mempty _T)) (\ v -> bind d v (f s b)), IntMap.insert m (free d) s)) (0, subst, IntMap.empty) metas


-- Classification

data Sort
  = STerm
  | SType
  | SKind
  deriving (Bounded, Enum, Eq, Ord, Show)

-- | Classifies values according to whether or not they describe types.
sortOf :: Stack Sort -> Value -> Sort
sortOf ctx = \case
  VType                       -> SKind
  VInterface                  -> SKind
  VForAll (Binding _ _ _T) _B -> let _T' = sortOf ctx ((type' :: Sig -> Value) _T) in min _T' (sortOf (ctx :> _T') (_B (free (Level (length ctx)))))
  VLam{}                      -> STerm
  VNeut h sp                  -> minimum (unVar (pred . sortOf ctx . ty) ((ctx !) . getIndex . levelToIndex (Level (length ctx))) (pred . sortOf ctx . ty) h : toList (sortOf ctx . out <$> sp))
  VCon _                      -> STerm


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
  , decls     :: [Decl]
  }

name_ :: Lens' Module MName
name_ = lens (\ Module{ name } -> name) (\ m name -> (m :: Module){ name })

imports_ :: Lens' Module [Import]
imports_ = lens imports (\ m imports -> m{ imports })

decls_ :: Lens' Module [Decl]
decls_ = lens decls (\ m decls -> m{ decls })


-- FIXME: produce multiple results, if they exist.
lookupC :: Has Empty sig m => UName -> Module -> m (QName :=: Maybe Def ::: Value)
lookupC n Module{ name, decls } = maybe empty pure $ matchWith matchDef decls
  where
  -- FIXME: insert the constructors into the top-level scope instead of looking them up under the datatype.
  matchDef (Decl _ d     _)  = (d >>= unDData >>= matchWith matchCon) <|> (d >>= unDInterface >>= matchWith matchCon)
  matchCon (n' :=: v ::: _T) = (name :.: C n' :=: Just (DTerm v) ::: _T) <$ guard (n == n')

-- FIXME: produce multiple results, if they exist.
lookupD :: Has Empty sig m => DName -> Module -> m (QName :=: Maybe Def ::: Value)
lookupD (C n) m = lookupC n m
lookupD n m@Module{ name = mname, decls } = maybe ((`lookupC` m) =<< unEName n) pure $ do
  Decl _ d _T <- find ((n ==) . (name :: Decl -> DName)) decls
  pure $ mname :.: n :=: d ::: _T


newtype Import = Import { name :: MName }

-- FIXME: keep track of free variables in declarations so we can work incrementally
data Decl = Decl
  { name  :: DName
  , def   :: Maybe Def
  , type' :: Value
  }

data Def
  = DTerm Value
  | DData [UName :=: Value ::: Value]
  | DInterface [UName :=: Value ::: Value]

unDData :: Has Empty sig m => Def -> m [UName :=: Value ::: Value]
unDData = \case
  DData cs -> pure cs
  _        -> empty

unDInterface :: Has Empty sig m => Def -> m [UName :=: Value ::: Value]
unDInterface = \case
  DInterface cs -> pure cs
  _             -> empty


matchWith :: Foldable t => (a -> Maybe b) -> t a -> Maybe b
matchWith rel = getFirst . foldMap (First . rel)
