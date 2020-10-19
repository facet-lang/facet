{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core
( -- * Values
  Value(..)
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
, subst
, bind
  -- * Patterns
, Pattern(..)
  -- * Modules
, Module(..)
, Def(..)
  -- * Quotation
, QExpr(..)
, quote
, eval
) where

import           Control.Effect.Empty
import           Data.Bifoldable
import           Data.Bifunctor
import           Data.Bitraversable
import           Data.Foldable (foldl')
import           Data.Function (on)
import qualified Data.IntMap as IntMap
import           Data.Monoid (First(..))
import           Data.Semialign
import           Data.Traversable (mapAccumL)
import           Facet.Name (CName, Index(..), Level(..), MName, Meta(..), QName, UName, levelToIndex)
import           Facet.Stack
import           Facet.Syntax
import           GHC.Stack
import           Prelude hiding (zip, zipWith)

-- Values

-- FIXME: represent closed portions of the tree explicitly?
data Value
  = VType
  | VForAll (Pl_ UName ::: Value) (Value -> Value)
  -- FIXME: consider type-indexed patterns & an existential clause wrapper to ensure name & variable patterns have the same static shape
  | VLam (Pl_ UName ::: Value) (Value -> Value)
  -- | Neutral terms are an unreduced head followed by a stack of eliminators.
  | VNeut (Head Value Level) (Stack Elim)
  | VCon (Con Value Value)

instance Eq Value where
  (==) = (==) `on` quote (Level 0)


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


-- Modules

data Module = Module MName [(QName, Def ::: Value)]

data Def
  = DTerm Value
  | DType Value
  | DData [CName ::: Value]


-- Quotation

data QExpr
  = QVar (Head QExpr Index)
  | QType
  | QForAll (Pl_ UName ::: QExpr) QExpr
  | QLam (Pl_ UName ::: QExpr) QExpr
  | QApp QExpr (Pl_ QExpr)
  | QCase QExpr [(Pattern QExpr (UName ::: QExpr), QExpr)]
  | QCon (Con QExpr QExpr)
  deriving (Eq, Ord, Show)

quote :: Level -> Value -> QExpr
quote d = \case
  VType -> QType
  VCon c -> QCon (bimap (quote d) (quote d) c)
  VLam (n ::: t) b -> QLam (n ::: quote d t) (quote (succ d) (b (var (Free d))))
  VForAll (n ::: t) b -> QForAll (n ::: quote d t) (quote (succ d) (b (var (Free d))))
  VNeut h sp ->
    let qSp h Nil     = h
        qSp h (sp:>e) = case e of
          EApp a   -> QApp (qSp h sp) (fmap (quote d) a)
          ECase cs -> QCase (qSp h sp) (map qClause cs)
        qClause (p, b)
          | let (d', p') = mapAccumL (\ d _ -> (succ d, var (Free d))) d p
          = ( bimap (quote d) (fmap (quote d)) p
            , quote d' (b p'))
    in qSp (QVar (unHead (Global . fmap (quote d)) (Free . levelToIndex d) (Metavar . fmap (quote d)) h)) sp

eval :: Stack Value -> QExpr -> Value
eval env = \case
  QType -> VType
  QCon c -> VCon (bimap (eval env) (eval env) c)
  QLam (n ::: t) b -> VLam (n ::: eval env t) (\ v -> eval (env:>v) b)
  QForAll (n ::: t) b -> VForAll (n ::: eval env t) (\ v -> eval (env:>v) b)
  QVar h -> unHead (global . fmap (eval env)) ((env !) . getIndex) (metavar . fmap (eval env)) h
  QApp f a -> eval env f $$ fmap (eval env) a
  QCase s cs -> case' (eval env s) (map (evalClause env) cs)
    where
    evalClause env (p, b) = (bimap (eval env) (fmap (eval env)) p, \ p -> eval (foldl' (:>) env p) b)
