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
, Head(..)
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
, mapValue
, mapValueAll
, join
, AValue(..)
, eq
) where

import           Control.Carrier.Empty.Church
import           Control.Carrier.Lift
import           Control.Monad ((<=<))
import           Data.Foldable (foldl', for_, toList)
import           Data.Functor (void)
import           Data.Monoid (First(..))
import           Data.Traversable (mapAccumL)
import           Facet.Core.Pattern
import           Facet.Functor.Eq
import           Facet.Name (Index(..), Level(..), QName, UName, isMeta, levelToIndex)
import           Facet.Stack hiding ((!))
import qualified Facet.Stack as S
import           Facet.Syntax
import           GHC.Stack

-- FIXME: eliminate TLam; track type introductions and applications with annotations in the context.
-- FIXME: replace :-> with syntax sugar for :=>.
-- FIXME: replace products, void, and unit with references to constant datatypes.
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
  | Local a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

unHead :: (QName -> b) -> (a -> b) -> Head a -> b
unHead f g = \case
  Global n -> f n
  Local  n -> g n


global :: QName -> Value f a
global n = Global n :$ Nil

bound :: a -> Value f a
bound n = Local n :$ Nil


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


-- | Map over the variables in a value bound by a given context & metacontext.
--
-- Note that this doesn’t have any argument mapping bound values to @a@; the idea is that instead, 'Level' can be mapped uniquely onto elements of the context and metacontext, and thus can resolve bound variables to their values in these contexts.
--
-- This can be iterated (cf 'mapValueAll') trivially, because:
--
-- 1. Only closed values can exist within an empty context and metacontext.
-- 2. No dependencies are allowed between the contexts.
-- 3. Values bound in a context can only depend on information earlier in the same context.
--
-- Thus, a value bound in the context is independent of anything following; so we can map the initial context values in the empty context, the next in the context consisting of the mapped initial values, and so on, all the way along.
mapValue :: (HasCallStack, Monad m) => [Value m a] -> Stack (Value m a) -> Value m Level -> m (Value m a)
-- FIXME: model contextualized values explicitly.
-- FIXME: m can extend the metacontext, invalidating this as we move under binders.
mapValue mctx = go
  where
  go ctx = \case
    Type     -> pure Type
    Void     -> pure Void
    TUnit    -> pure TUnit
    Unit     -> pure Unit
    t :=> b  -> do
      t' <- traverse (go ctx) t
      pure $ t' :=> bind ctx b
    a :-> b  -> (:->) <$> go ctx a <*> go ctx b
    TLam n b -> pure $ TLam n $ bind ctx b
    Lam  ps  -> pure $ Lam $ map (\ (p, b) -> (p, bindP ctx b)) ps
    f :$ as  -> do
      let f' = unHead global (lookupIn ctx) f
      as' <- traverse (go ctx) as
      f' $$* as'
    TPrd l r -> TPrd <$> go ctx l <*> go ctx r
    Prd  l r -> Prd  <$> go ctx l <*> go ctx r
  bind ctx b = \ v -> do
    b' <- b (bound (Level (length ctx)))
    go (ctx :> v) b'
  bindP ctx b = \ v -> do
    let (ctx', v') = mapAccumL (\ ctx v -> (ctx :> v, bound (Level (length ctx)))) ctx v
    b' <- b v'
    go ctx' b'
  lookupIn ctx l
    | isMeta l  = mctx !! abs (getIndex (levelToIndex mlevel l) + 1)
    | otherwise = ctx S.! getIndex (levelToIndex (Level (length ctx)) l)
  mlevel = Level (length mctx)

mapValueAll :: (HasCallStack, Monad m) => [Value m Level] -> Stack (Value m Level) -> m ([Value m a], Stack (Value m a))
mapValueAll mctx ctx = go ctx
  where
  metas []     = pure []
  metas (m:ms) = do
    ms' <- metas ms
    m'  <- mapValue ms' Nil m
    pure $ m' : ms'
  go Nil     = do
    mctx' <- metas mctx
    pure (mctx', Nil)
  go (as:>a) = do
    (mctx', as') <- go as
    a' <- mapValue mctx' as' a
    pure (mctx', as' :> a')


join :: Monad m => Value m (Value m a) -> m (Value m a)
join = \case
  Type     -> pure Type
  Void     -> pure Void
  TUnit    -> pure TUnit
  Unit     -> pure Unit
  t :=> b  -> do
    t' <- traverse join t
    pure $ t' :=> bind b
  TLam n b -> pure $ TLam n (bind b)
  a :-> b  -> (:->) <$> join a <*> join b
  Lam cs   -> pure $ Lam (map (fmap bindP) cs)
  f :$ as  -> (unHead global id f $$*) =<< traverse join as
  TPrd l r -> TPrd <$> join l <*> join r
  Prd  l r -> Prd  <$> join l <*> join r
  where
  bind  b = join <=< b . bound
  bindP b = join <=< b . fmap bound


newtype AValue f = AValue { runAValue :: forall x . Value f x }


eq :: Monad m => AValue m -> AValue m -> m Bool
eq v1 v2 = eqM @_ @Int (runAValue v1) (runAValue v2)
