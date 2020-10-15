{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core.Value
( Value(..)
, Head(Global, Local)
, unHead
, global
, bound
, unForAll
, unTLam
, unArrow
, unLam
, unProductT
, ($$)
, ($$*)
, case'
, match
, handle
, handleBinder
, handleBinderP
, AValue(..)
, eq
) where

import           Control.Carrier.Empty.Church
import           Control.Carrier.Lift
import           Control.Monad ((<=<))
import           Data.Foldable (foldl', for_, toList)
import           Data.Functor (void)
import qualified Data.IntMap as IntMap
import           Data.Monoid (First(..))
import           Data.Traversable (mapAccumL)
import           Facet.Core.Pattern
import           Facet.Functor.Eq
import           Facet.Name (Level(..), QName, UName, incrLevel)
import           Facet.Stack
import           Facet.Syntax
import           GHC.Stack

-- FIXME: eliminate TLam; track type introductions and applications with annotations in the context.
-- FIXME: replace :-> with syntax sugar for :=>.
-- FIXME: replace products, void, and unit with references to constant datatypes.
-- FIXME: represent closed portions of the tree explicitly?
data Value f a
  = Type
  | Void
  | TUnit
  | Unit
  | (UName ::: Value f a) :=> (Value f a -> f (Value f a))
  | TLam UName (Value f a -> f (Value f a))
  | Value f a :-> Value f a
  -- FIXME: consider type-indexed patterns & an existential clause wrapper to ensure name & variable patterns have the same static shape
  | Lam [(Pattern UName, Pattern (Value f a) -> f (Value f a))]
  | Head a :$ Stack (Value f a)
  | TPrd (Value f a) (Value f a)
  | Prd (Value f a) (Value f a)

infixr 1 :=>
infixl 9 :$
infixr 1 :->

instance (Eq a, Num a) => EqM Value a where
  eqM v1 v2 = runM (execEmpty (go 0 v1 v2))
    where
    -- defined thus to get the exhaustiveness checker to ensure I don’t miss adding new cases
    go n = curry $ \case
      (Type, Type) -> pure ()
      (Type, _) -> empty
      (Void, Void) -> pure ()
      (Void, _) -> empty
      (TUnit, TUnit) -> pure ()
      (TUnit, _) -> empty
      (Unit, Unit) -> pure ()
      (Unit, _) -> empty
      (t1 :=> b1, t2 :=> b2) -> do
        go n (ty t1) (ty t2)
        b1' <- sendM $ b1 (bound n)
        b2' <- sendM $ b2 (bound n)
        go (n + 1) b1' b2'
      (_ :=> _, _) -> empty
      (TLam _ b1, TLam _ b2) -> do
        b1' <- sendM $ b1 (bound n)
        b2' <- sendM $ b2 (bound n)
        go (n + 1) b1' b2'
      (TLam _ _, _) -> empty
      (Lam c1, Lam c2)
        | length c1 == length c2 -> do
          for_ (zip c1 c2) $ \ ((p1, b1), (p2, b2)) -> guard (void p1 == void p2) *> do
            let (n', p') = mapAccumL (\ n _ -> (n + 1, bound n)) n p2
            b1' <- sendM $ b1 p'
            b2' <- sendM $ b2 p'
            go n' b1' b2'
      (Lam _, _) -> empty
      (f1 :$ as1, f2 :$ as2)
        | f1 == f2
        , length as1 == length as2 ->
          for_ (zip (toList as1) (toList as2)) (uncurry (go n))
      (_ :$ _, _) -> empty
      (a1 :-> b1, a2 :-> b2) -> go n a1 a2 *> go n b1 b2
      (_ :-> _, _) -> empty
      (TPrd l1 r1, TPrd l2 r2) -> go n l1 l2 *> go n r1 r2
      (TPrd _ _, _) -> empty
      (Prd l1 r1, Prd l2 r2) -> go n l1 l2 *> go n r1 r2
      (Prd _ _, _) -> empty


data Head a
  = Global QName
  | Local a -- FIXME: this should actually be Free
  | Quote Level
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

unHead :: (QName -> b) -> (a -> b) -> (Level -> b) -> Head a -> b
unHead f g h = \case
  Global n -> f n
  Local  n -> g n
  Quote  n -> h n


global :: QName -> Value f a
global = var . Global

-- FIXME: this should actually be free
bound :: a -> Value f a
bound = var . Local

quote :: Level -> Value f a
quote = var . Quote


var :: Head a -> Value f a
var = (:$ Nil)


unForAll :: Has Empty sig m => Value f a -> m (UName ::: Value f a, Value f a -> f (Value f a))
unForAll = \case{ t :=> b -> pure (t, b) ; _ -> empty }

unTLam :: Has Empty sig m => Value f a -> m (UName, Value f a -> f (Value f a))
unTLam = \case{ TLam n b -> pure (n, b) ; _ -> empty }

unArrow :: Has Empty sig m => Value f a -> m (Value f a, Value f a)
unArrow = \case{ a :-> b -> pure (a, b) ; _ -> empty }

unLam :: Has Empty sig m => Value f a -> m [(Pattern UName, Pattern (Value f a) -> f (Value f a))]
unLam = \case{ Lam ps -> pure ps ; _ -> empty }

unProductT :: Has Empty sig m => Value f a -> m (Value f a, Value f a)
unProductT = \case{ TPrd l r -> pure (l, r) ; _ -> empty }


-- FIXME: how should this work in weak/parametric HOAS?
($$) :: (HasCallStack, Applicative f) => Value f a -> Value f a -> f (Value f a)
(f :$ as) $$ a = pure (f :$ (as :> a))
(_ :=> b) $$ a = b a
TLam _ b  $$ a = b a
Lam    ps $$ a = case' a ps
_         $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (HasCallStack, Foldable t, Monad f) => Value f a -> t (Value f a) -> f (Value f a)
f $$* as = foldl' (\ f a -> f >>= ($$ a)) (pure f) as

infixl 9 $$, $$*


case' :: HasCallStack => Value f a -> [(Pattern UName, Pattern (Value f a) -> f (Value f a))] -> f (Value f a)
case' s ps = case getFirst (foldMap (\ (p, f) -> First $ f <$> match s p) ps) of
  Just v -> v
  _      -> error "non-exhaustive patterns in lambda"

match :: Value f a -> Pattern UName -> Maybe (Pattern (Value f a))
match s = \case
  Wildcard         -> Just Wildcard
  Var _            -> Just (Var s)
  Tuple [pl, pr]
    | Prd l r <- s -> do
      l' <- match l pl
      r' <- match r pr
      Just $ Tuple [l', r']
  _                -> Nothing


handle :: (HasCallStack, Monad m, Monad n) => Value m a -> m (Value n a)
handle = go (Level 0)
  where
  go d = \case
    Type     -> pure Type
    Void     -> pure Void
    TUnit    -> pure TUnit
    Unit     -> pure Unit
    t :=> b  -> do
      t' <- traverse (go d) t
      b' <- go (incrLevel d) =<< b (quote d)
      pure $ t' :=> bind d b'
    TLam n b -> do
      b' <- go (incrLevel d) =<< b (quote d)
      pure $ TLam n (bind d b')
    a :-> b  -> (:->) <$> go d a <*> go d b
    Lam cs   -> do
      cs' <- traverse (\ (p, b) -> do
        let (d', p') = mapAccumL (\ d _ -> (incrLevel d, quote d)) d p
        b' <- go d' =<< b p'
        pure (p, \ v -> subst (snd (foldr (\ v (d, s) -> (incrLevel d, IntMap.insert (getLevel d) v s)) (d, IntMap.empty) v)) b')) cs
      pure $ Lam cs'
    f :$ as  -> (f :$) <$> traverse (go d) as
    TPrd l r -> TPrd <$> go d l <*> go d r
    Prd  l r -> Prd  <$> go d l <*> go d r
  bind d b = (`subst` b) . IntMap.singleton (getLevel d)

handleBinder :: (HasCallStack, Monad m, Monad n) => Level -> (Value n a -> m (Value n a)) -> m (Value n a -> n (Value n a))
handleBinder d b = do
  b' <- b (quote d)
  pure $ (`subst` b') . IntMap.singleton (getLevel d)

handleBinderP :: (HasCallStack, Monad m, Monad n, Traversable t) => Level -> t x -> (t (Value n a) -> m (Value n a)) -> m (t (Value n a) -> n (Value n a))
handleBinderP d p b = do
  let (_, p') = mapAccumL (\ d _ -> (incrLevel d, quote d)) d p
  b' <- b p'
  pure $ \ v -> subst (snd (foldr (\ v (d, s) -> (incrLevel d, IntMap.insert (getLevel d) v s)) (d, IntMap.empty) v)) b'

-- FIXME: is it possible to instead perform one complete substitution at the end of handle?
subst :: (HasCallStack, Monad m) => IntMap.IntMap (Value m a) -> Value m a -> m (Value m a)
subst s = go
  where
  go = \case
    Type     -> pure Type
    Void     -> pure Void
    TUnit    -> pure TUnit
    Unit     -> pure Unit
    t :=> b  -> do
      t' <- traverse go t
      pure $ t' :=> go <=< b
    TLam n b -> pure $ TLam n (go <=< b)
    a :-> b  -> (:->) <$> go a <*> go b
    Lam cs   -> pure $ Lam (map (fmap (go <=<)) cs)
    f :$ as  -> (unHead global bound (s !) f $$*) =<< traverse go as
    TPrd l r -> TPrd <$> go l <*> go r
    Prd  l r -> Prd  <$> go l <*> go r
  s ! l = case IntMap.lookup (getLevel l) s of
    Just a  -> a
    Nothing -> quote l


newtype AValue f = AValue { runAValue :: forall x . Value f x }


eq :: Monad m => AValue m -> AValue m -> m Bool
eq v1 v2 = eqM @_ @Int (runAValue v1) (runAValue v2)
