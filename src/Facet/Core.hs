module Facet.Core
( -- * Values
  Value(..)
, Sig(..)
, Head(..)
, Elim(..)
, Con(..)
, unHead
, global
, free
, metavar
, unForAll
, unForAll'
, unLam
, unLam'
, ($$)
, case'
, match
, elim
, elimN
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
  -- * Modules
, Module(..)
, Import(..)
, Def(..)
) where

import           Control.Effect.Empty
import           Data.Bifoldable
import           Data.Bifunctor
import           Data.Bitraversable
import           Data.Foldable (foldl', toList)
import qualified Data.IntMap as IntMap
import           Data.Monoid (First(..))
import           Data.Semialign
import           Data.Traversable (mapAccumL)
import           Facet.Name hiding (bind)
import           Facet.Stack
import           Facet.Syntax
import           GHC.Stack
import           Prelude hiding (zip, zipWith)

-- Values

-- FIXME: represent closed portions of the tree explicitly?
data Value
  = VType
  | VForAll (Pl_ UName ::: Value) (Value -> Value)
  | VLam (Pl_ UName ::: Value) (Value -> Value)
  -- | Neutral terms are an unreduced head followed by a stack of eliminators.
  | VNeut (Head Value Level) (Stack Elim)
  | VCon (Con Value Value)

instance Eq Value where
  (==) = eq (Level 0)

eq :: Level -> Value -> Value -> Bool
eq d = curry $ \case
  -- defined thus instead of w/ fallback case to have exhaustiveness checks kick in when adding constructors.
  (VType, VType)                                           -> True
  (VType, _)                                               -> False
  (VForAll (P p1 _ ::: t1) b1, VForAll (P p2 _ ::: t2) b2) -> p1 == p2 && eq d t1 t2 && eq (succ d) (b1 (free d)) (b2 (free d))
  (VForAll{}, _)                                           -> False
  (VLam (P p1 _ ::: t1) b1, VLam (P p2 _ ::: t2) b2)       -> p1 == p2 && eq d t1 t2 && eq (succ d) (b1 (free d)) (b2 (free d)) -- FIXME: do we need to test the types here?
  (VLam{}, _)                                              -> False
  (VNeut h1 sp1, VNeut h2 sp2)                             -> eqH d h1 h2 && eqSp d sp1 sp2
  (VNeut{}, _)                                             -> False
  (VCon c1, VCon c2)                                       -> eqCon eq d c1 c2
  (VCon _, _)                                              -> False
  where
  eqH d = curry $ \case
    (Global (q1 ::: t1), Global (q2 ::: t2))   -> q1 == q2 && eq d t1 t2
    (Global _, _)                              -> False
    (Free d1, Free d2)                         -> d1 == d2
    (Free _, _)                                -> False
    (Metavar (m1 ::: t1), Metavar (m2 ::: t2)) -> m1 == m2 && eq d t1 t2
    (Metavar _, _)                             -> False
  eqSp d sp1 sp2 = length sp1 == length sp2 && and (zipWith (eqElim d) sp1 sp2)
  eqElim d = curry $ \case
    (EApp (P p1 a1), EApp (P p2 a2)) -> p1 == p2 && eq d a1 a2
    (EApp _, _)                      -> False
    (ECase cs1, ECase cs2)           -> length cs1 == length cs2 && and (zipWith (eqClause d) cs1 cs2)
    (ECase _, _)                     -> False
  eqClause d (p1, b1) (p2, b2) = eqPat d p1 p2 && eq (succ d) (b1 (PVar (free d))) (b2 (PVar (free d)))
  eqPat d = curry $ \case
    (PVar (_ ::: t1), PVar (_ ::: t2)) -> eq d t1 t2
    (PVar _, _)                        -> False
    (PCon c1, PCon c2)                 -> eqCon eqPat d c1 c2
    (PCon _, _)                        -> False
  eqCon :: (Level -> a -> b -> Bool) -> Level -> Con Value a -> Con Value b -> Bool
  eqCon eq' d (Con (n1 ::: t1) fs1) (Con (n2 ::: t2) fs2) = n1 == n2 && eq d t1 t2 && length fs1 == length fs2 && and (zipWith (eq' d) fs1 fs2)


data Sig = Sig


data Head t a
  = Global (QName ::: t) -- ^ Global variables, considered equal by 'QName'.
  | Free a
  | Metavar (Meta ::: t) -- ^ Metavariables, considered equal by 'Level'.
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

unHead :: (QName ::: t -> b) -> (a -> b) -> (Meta ::: t -> b) -> Head t a -> b
unHead f g h = \case
  Global  n -> f n
  Free    n -> g n
  Metavar n -> h n


data Elim
  = EApp (Pl_ Value) -- FIXME: this is our one codata case; should we generalize this to copattern matching?
  -- FIXME: consider type-indexed patterns & an existential clause wrapper to ensure name & variable patterns have the same static shape
  | ECase [(Pattern Value (UName ::: Value), Pattern Value Value -> Value)] -- FIXME: we can (and should) eliminate var patterns eagerly.


data Con t a = Con (QName ::: t) (Stack a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bifoldable Con where
  bifoldMap = bifoldMapDefault

instance Bifunctor Con where
  bimap = bimapDefault

instance Bitraversable Con where
  bitraverse f g (Con t b) = Con <$> traverse f t <*> traverse g b


global :: QName ::: Value -> Value
global = var . Global

free :: Level -> Value
free = var . Free

metavar :: Meta ::: Value -> Value
metavar = var . Metavar


var :: Head Value Level -> Value
var = (`VNeut` Nil)


unForAll :: Has Empty sig m => Value -> m (Pl_ UName ::: Value, Value -> Value)
unForAll = \case{ VForAll t b -> pure (t, b) ; _ -> empty }

-- | A variation on 'unForAll' which can be conveniently chained with 'splitr' to strip a prefix of quantifiers off their eventual body.
unForAll' :: Has Empty sig m => (Level, Value) -> m (Pl_ UName ::: Value, (Level, Value))
unForAll' (d, v) = do
  (_T, _B) <- unForAll v
  pure (_T, (succ d, _B (free d)))

unLam :: Has Empty sig m => Value -> m (Pl_ UName ::: Value, Value -> Value)
unLam = \case{ VLam n b -> pure (n, b) ; _ -> empty }

-- | A variation on 'unLam' which can be conveniently chained with 'splitr' to strip a prefix of lambdas off their eventual body.
unLam' :: Has Empty sig m => (Level, Value) -> m (Pl_ UName ::: Value, (Level, Value))
unLam' (d, v) = do
  (n, t) <- unLam v
  pure (n, (succ d, t (free d)))


-- FIXME: how should this work in weak/parametric HOAS?
($$) :: HasCallStack => Value -> Pl_ Value -> Value
VNeut h es  $$ a = VNeut h (es :> EApp a)
VForAll _ b $$ a = b (out a)
VLam _    b $$ a = b (out a)
_           $$ _ = error "can’t apply non-neutral/forall type"

infixl 9 $$


case' :: HasCallStack => Value -> [(Pattern Value (UName ::: Value), Pattern Value Value -> Value)] -> Value
case' s            cs
  | (p, f):_ <- cs
  , PVar _ <- p       = f (PVar s)
case' (VNeut h es) cs = VNeut h (es :> ECase cs)
case' s            cs = case getFirst (foldMap (\ (p, f) -> First $ f <$> match s p) cs) of
  Just v -> v
  _      -> error "non-exhaustive patterns in lambda"

match :: Value -> Pattern Value b -> Maybe (Pattern Value Value)
match = curry $ \case
  (s,          PVar _)                -> Just (PVar s)
  (VCon (Con n' fs), PCon (Con n ps)) -> do
    guard (tm n == tm n')
    -- NB: we’re assuming they’re the same length because they’ve passed elaboration.
    PCon . Con n' <$> sequenceA (zipWith match fs ps)
  (_,          PCon _)                -> Nothing


elim :: HasCallStack => Value -> Elim -> Value
elim v = \case
  EApp a   -> v $$ a
  ECase cs -> case' v cs

elimN :: (HasCallStack, Foldable t) => Value -> t Elim -> Value
elimN f as = foldl' elim f as


-- | Substitute metavars.
subst :: HasCallStack => IntMap.IntMap Value -> Value -> Value
subst s
  | IntMap.null s = id
  | otherwise     = go
  where
  go = \case
    VType       -> VType
    VForAll t b -> VForAll (fmap go t) (go . b)
    VLam    n b -> VLam (fmap go n) (go . b)
    VNeut f a   -> unHead global free (s !) f' `elimN` fmap substElim a
      where
      f' = case f of
        Global  (n ::: _T) -> Global  (n ::: go _T)
        Free    v          -> Free    v
        Metavar (d ::: _T) -> Metavar (d ::: go _T)
    VCon c      -> VCon (bimap go go c)

  substElim = \case
    EApp a   -> EApp (fmap go a)
    ECase cs -> ECase (map (bimap (bimap go (fmap go)) (go .)) cs)

  s ! l = case IntMap.lookup (getMeta (tm l)) s of
    Just a  -> a
    Nothing -> metavar l

-- | Bind a free variable.
bind :: HasCallStack => Level -> Value -> Value -> Value
bind target with = go
  where
  go = \case
    VType       -> VType
    VForAll t b -> VForAll (fmap go t) (go . b)
    VLam    n b -> VLam (fmap go n) (go . b)
    VNeut f a   -> unHead global (\ v -> if v == target then with else free v) metavar f' `elimN` fmap elim a
      where
      f' = case f of
        Global  (n ::: _T) -> Global  (n ::: go _T)
        Free    v          -> Free    v
        Metavar (d ::: _T) -> Metavar (d ::: go _T)
    VCon c      -> VCon (bimap go go c)

  elim = \case
    EApp a   -> EApp (fmap go a)
    ECase cs -> ECase (map (bimap (bimap go (fmap go)) (go .)) cs)


mvs :: Level -> Value -> IntMap.IntMap Value
mvs d = \case
  VType                   -> mempty
  VForAll (_ ::: t) b     -> mvs d t <> mvs (succ d) (b (free d))
  VLam (_ ::: t) b        -> mvs d t <> mvs (succ d) (b (free d))
  VNeut h sp              -> unHead (mvs d . ty) mempty (\ (m ::: _T) -> IntMap.insert (getMeta m) _T (mvs d _T)) h <> foldMap goE sp
    where
    goE = \case
      EApp a   -> foldMap (mvs d) a
      ECase cs -> foldMap goClause cs
    goClause (p, b) = bifoldMap (mvs d) (mvs d . ty) p <> let (d', p') = fill ((,) . succ <*> free) d p in  mvs d' (b p')
  VCon (Con (_ ::: t) fs) -> mvs d t <> foldMap (mvs d) fs


generalize :: Value -> Value
generalize v = build s v
  where
  metas = mvs (Level 0) v
  (_, build, s) = IntMap.foldrWithKey (\ m _T (d, f, s) -> (succ d, \ s b -> VForAll (im __ ::: _T) (\ v -> bind d v (f s b)), IntMap.insert m (free d) s)) (Level 0, subst, IntMap.empty) metas


-- Classification

data Sort
  = STerm
  | SType
  | SKind
  deriving (Bounded, Enum, Eq, Ord, Show)

-- | Classifies values according to whether or not they describe types.
sortOf :: Stack Sort -> Value -> Sort
sortOf ctx = \case
  VType                 -> SKind
  VForAll (_ ::: _T) _B -> let _T' = sortOf ctx _T in min _T' (sortOf (ctx :> _T') (_B (free (Level (length ctx)))))
  VLam{}                -> STerm
  VNeut h sp            -> minimum (unHead (pred . sortOf ctx . ty) ((ctx !) . getIndex . levelToIndex (Level (length ctx))) (pred . sortOf ctx . ty) h : toList (\case{ EApp a -> sortOf ctx (out a) ; ECase _ -> STerm } <$> sp))
  VCon _                -> STerm


-- Patterns

-- FIXME: eliminate this by unrolling cases into shallow, constructor-headed matches
data Pattern t a
  = PVar a
  | PCon (Con t (Pattern t a))
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bifoldable Pattern where
  bifoldMap = bifoldMapDefault

instance Bifunctor Pattern where
  bimap = bimapDefault

instance Bitraversable Pattern where
  bitraverse f g = go
    where
    go = \case
      PVar a -> PVar <$> g a
      PCon c -> PCon <$> bitraverse f go c

fill :: Traversable t => (b -> (b, c)) -> b -> t a -> (b, t c)
fill f z = mapAccumL (\ z _ -> f z) z


-- Modules

data Module = Module
  { name    :: MName
  , imports :: [Import]
  , defs    :: [(QName, Def ::: Value)]
  }

newtype Import = Import { name :: MName }

data Def
  = DTerm Value
  | DData [UName :=: Value ::: Value]
