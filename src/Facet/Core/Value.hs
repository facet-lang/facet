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
, Head(Global, Local, Metavar)
, unHead
, global
, bound
, metavar
, unForAll
, unArrow
, unLam
, unProductT
, ($$)
, ($$*)
, case'
, match
, handleBinder
, handleBinderP
, subst
, AValue(..)
, Contextual(..)
) where

import           Control.Effect.Empty
import           Data.Foldable (foldl', toList)
import           Data.Functor (void)
import qualified Data.IntMap as IntMap
import           Data.Monoid (First(..))
import           Data.Traversable (mapAccumL)
import qualified Facet.Context as Ctx
import           Facet.Core.Pattern
import           Facet.Name (Level(..), QName, UName)
import           Facet.Stack
import           Facet.Syntax
import           GHC.Stack

-- FIXME: replace :-> with syntax sugar for :=>.
-- FIXME: replace products, void, and unit with references to constant datatypes.
-- FIXME: represent closed portions of the tree explicitly?
data Value a
  = Type
  | Void
  | TUnit
  | Unit
  | (UName ::: Value a) :=> (Value a -> Value a)
  | Value a :-> Value a
  -- FIXME: consider type-indexed patterns & an existential clause wrapper to ensure name & variable patterns have the same static shape
  | Lam [(Pattern UName, Pattern (Value a) -> (Value a))]
  | Head a :$ Stack (Value a)
  | TPrd (Value a) (Value a)
  | Prd (Value a) (Value a)

infixr 1 :=>
infixl 9 :$
infixr 1 :->

instance (Eq a, Num a) => Eq (Value a) where
  v1 == v2 = go 0 v1 v2
    where
    -- defined thus to get the exhaustiveness checker to ensure I don’t miss adding new cases
    go n = curry $ \case
      (Type, Type) -> True
      (Type, _) -> False
      (Void, Void) -> True
      (Void, _) -> False
      (TUnit, TUnit) -> True
      (TUnit, _) -> False
      (Unit, Unit) -> True
      (Unit, _) -> False
      (t1 :=> b1, t2 :=> b2) ->
        go n (ty t1) (ty t2)
        &&  let b1' = b1 (bound n)
                b2' = b2 (bound n)
            in go (n + 1) b1' b2'
      (_ :=> _, _) -> False
      (Lam c1, Lam c2)
        | length c1 == length c2 -> do
          and (zipWith (eqPat n) c1 c2)
      (Lam _, _) -> False
      (f1 :$ as1, f2 :$ as2)
        | f1 == f2
        , length as1 == length as2 ->
          and (zipWith (go n) (toList as1) (toList as2))
      (_ :$ _, _) -> False
      (a1 :-> b1, a2 :-> b2) -> go n a1 a2 && go n b1 b2
      (_ :-> _, _) -> False
      (TPrd l1 r1, TPrd l2 r2) -> go n l1 l2 && go n r1 r2
      (TPrd _ _, _) -> False
      (Prd l1 r1, Prd l2 r2) -> go n l1 l2 && go n r1 r2
      (Prd _ _, _) -> False
    eqPat n (p1, b1) (p2, b2)
      =   void p1 == void p2
      &&  let (n', p') = mapAccumL (\ n _ -> (n + 1, bound n)) n p2
              b1' = b1 p'
              b2' = b2 p'
          in go n' b1' b2'


data Head a
  = Global QName
  | Local a -- FIXME: this should actually be Free
  | Quote Level
  | Metavar Level
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

unHead :: (QName -> b) -> (a -> b) -> (Level -> b) -> (Level -> b) -> Head a -> b
unHead f g h i = \case
  Global  n -> f n
  Local   n -> g n
  Quote   n -> h n
  Metavar n -> i n


global :: QName -> Value a
global = var . Global

-- FIXME: this should actually be free
bound :: a -> Value a
bound = var . Local

quote :: Level -> Value a
quote = var . Quote

metavar :: Level -> Value a
metavar = var . Metavar


var :: Head a -> Value a
var = (:$ Nil)


unForAll :: Has Empty sig m => Value a -> m (UName ::: Value a, Value a -> Value a)
unForAll = \case{ t :=> b -> pure (t, b) ; _ -> empty }

unArrow :: Has Empty sig m => Value a -> m (Value a, Value a)
unArrow = \case{ a :-> b -> pure (a, b) ; _ -> empty }

unLam :: Has Empty sig m => Value a -> m [(Pattern UName, Pattern (Value a) -> Value a)]
unLam = \case{ Lam ps -> pure ps ; _ -> empty }

unProductT :: Has Empty sig m => Value a -> m (Value a, Value a)
unProductT = \case{ TPrd l r -> pure (l, r) ; _ -> empty }


-- FIXME: how should this work in weak/parametric HOAS?
($$) :: HasCallStack => Value a -> Value a -> Value a
(f :$ as) $$ a = f :$ (as :> a)
(_ :=> b) $$ a = b a
Lam    ps $$ a = case' a ps
_         $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (HasCallStack, Foldable t) => Value a -> t (Value a) -> Value a
f $$* as = foldl' ($$) f as

infixl 9 $$, $$*


case' :: HasCallStack => Value a -> [(Pattern UName, Pattern (Value a) -> Value a)] -> Value a
case' s ps = case getFirst (foldMap (\ (p, f) -> First $ f <$> match s p) ps) of
  Just v -> v
  _      -> error "non-exhaustive patterns in lambda"

match :: Value a -> Pattern UName -> Maybe (Pattern (Value a))
match s = \case
  Wildcard         -> Just Wildcard
  Var _            -> Just (Var s)
  Tuple [pl, pr]
    | Prd l r <- s -> do
      l' <- match l pl
      r' <- match r pr
      Just $ Tuple [l', r']
  _                -> Nothing


handleBinder :: (HasCallStack, Monad m) => Level -> (Value a -> m (Value a)) -> m (Value a -> Value a)
handleBinder d b = do
  b' <- b (quote d)
  pure $ (`subst` b') . IntMap.singleton (getLevel d)

handleBinderP :: (HasCallStack, Monad m, Traversable t) => Level -> t x -> (t (Value a) -> m (Value a)) -> m (t (Value a) -> Value a)
handleBinderP d p b = do
  let (_, p') = mapAccumL (\ d _ -> (succ d, quote d)) d p
  b' <- b p'
  pure $ \ v -> subst (snd (foldr (\ v (d, s) -> (succ d, IntMap.insert (getLevel d) v s)) (d, IntMap.empty) v)) b'

-- FIXME: is it possible to instead perform one complete substitution at the end of <whatever>?
subst :: HasCallStack => IntMap.IntMap (Value a) -> Value a -> Value a
subst s = go
  where
  go = \case
    Type     -> Type
    Void     -> Void
    TUnit    -> TUnit
    Unit     -> Unit
    t :=> b  ->
      let t' = fmap go t
      in t' :=> go . b
    a :-> b  -> go a :-> go b
    Lam cs   -> Lam (map (fmap (go .)) cs)
    f :$ as  -> unHead global bound (s !) metavar f $$* fmap go as
    TPrd l r -> TPrd (go l) (go r)
    Prd  l r -> Prd  (go l) (go r)
  s ! l = case IntMap.lookup (getLevel l) s of
    Just a  -> a
    Nothing -> quote l


newtype AValue = AValue { runAValue :: forall x . Value x }

instance Eq AValue where
  v1 == v2 = (runAValue v1 :: Value Int) == (runAValue v2)


newtype Contextual f = Contextual { runContextual :: forall x . Ctx.Context (Value x ::: Value x) :|-: f x }
