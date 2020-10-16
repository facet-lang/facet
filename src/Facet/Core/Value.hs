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
, Elim(..)
, unHead
, global
, bound
, metavar
, unForAll
, unLam
, unProductT
, ($$)
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
import           Facet.Name (Level(..), PlName(..), QName, UName)
import           Facet.Stack
import           Facet.Syntax
import           GHC.Stack

-- FIXME: replace products, void, and unit with references to constant datatypes.
-- FIXME: represent closed portions of the tree explicitly?
data Value a
  = Type
  | Void
  | TUnit
  | Unit
  | (PlName ::: Value a) :=> (Value a -> Value a)
  -- FIXME: consider type-indexed patterns & an existential clause wrapper to ensure name & variable patterns have the same static shape
  | Lam PlName (Value a -> Value a)
  -- | Neutral terms are an unreduced head followed by a stack of eliminators.
  | Neut (Head a) (Stack (Elim (Value a)))
  | TPrd (Value a) (Value a)
  | Prd (Value a) (Value a)

infixr 1 :=>

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
        pl (tm t1) == pl (tm t2) && go n (ty t1) (ty t2)
        &&  let b1' = b1 (bound n)
                b2' = b2 (bound n)
            in go (n + 1) b1' b2'
      (_ :=> _, _) -> False
      (Lam _ b1, Lam _ b2) ->
        let b1' = b1 (bound n)
            b2' = b2 (bound n)
        in go (n + 1) b1' b2'
      (Lam _ _, _) -> False
      (Neut h1 sp1, Neut h2 sp2) -> h1 == h2 && eqSp n sp1 sp2
      (Neut _ _, _) -> False
      (TPrd l1 r1, TPrd l2 r2) -> go n l1 l2 && go n r1 r2
      (TPrd _ _, _) -> False
      (Prd l1 r1, Prd l2 r2) -> go n l1 l2 && go n r1 r2
      (Prd _ _, _) -> False
    eqSp n (sp1:>e1) (sp2:>e2) = eqSp n sp1 sp2 && eqElim n e1 e2
    eqSp _ Nil       Nil       = True
    eqSp _ _         _         = False
    eqElim n = curry $ \case
      (App a1, App a2) -> go n a1 a2
      (App _, _) -> False
      (Case cs1, Case cs2)
        | length cs1 == length cs2 -> and (zipWith (eqPat n) (toList cs1) (toList cs2))
      (Case _, _) -> False
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


data Elim a
  = App a -- FIXME: this is our one codata case; should we generalize this to copattern matching?
  | Case [(Pattern UName, Pattern a -> a)]


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
var = (`Neut` Nil)


unForAll :: Has Empty sig m => Value a -> m (PlName ::: Value a, Value a -> Value a)
unForAll = \case{ t :=> b -> pure (t, b) ; _ -> empty }

unLam :: Has Empty sig m => Value a -> m (PlName, Value a -> Value a)
unLam = \case{ Lam n b -> pure (n, b) ; _ -> empty }

unProductT :: Has Empty sig m => Value a -> m (Value a, Value a)
unProductT = \case{ TPrd l r -> pure (l, r) ; _ -> empty }


-- FIXME: how should this work in weak/parametric HOAS?
($$) :: HasCallStack => Value a -> Value a -> Value a
Neut h es $$ a = Neut h (es :> App a)
(_ :=> b) $$ a = b a
Lam _  b  $$ a = b a
_         $$ _ = error "can’t apply non-neutral/forall type"

infixl 9 $$


case' :: HasCallStack => Value a -> [(Pattern UName, Pattern (Value a) -> Value a)] -> Value a
case' (Neut h es) cs = Neut h (es :> Case cs)
case' s           cs = case getFirst (foldMap (\ (p, f) -> First $ f <$> match s p) cs) of
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


elim :: HasCallStack => Value a -> Elim (Value a) -> Value a
elim v = \case
  App a   -> v $$ a
  Case cs -> case' v cs

elimN :: (HasCallStack, Foldable t) => Value a -> t (Elim (Value a)) -> Value a
elimN f as = foldl' elim f as


-- FIXME: should we use metavars for quoted variables instead? they’d stand out and we’re going to substitute for them anyway…
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
    Lam n b  -> Lam n (go . b)
    Neut f a -> unHead global bound (s !) metavar f `elimN` fmap substElim a
    TPrd l r -> TPrd (go l) (go r)
    Prd  l r -> Prd  (go l) (go r)
  substElim = \case
    App a   -> App (go a)
    Case cs -> Case (map (fmap (go .)) cs)
  s ! l = case IntMap.lookup (getLevel l) s of
    Just a  -> a
    Nothing -> quote l


newtype AValue = AValue { runAValue :: forall x . Value x }

instance Eq AValue where
  v1 == v2 = (runAValue v1 :: Value Int) == (runAValue v2)


newtype Contextual f = Contextual { runContextual :: forall x . Ctx.Context (Value x ::: Value x) :|-: f x }
