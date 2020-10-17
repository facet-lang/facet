{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core
( -- * Values
  Value(..)
, Head(Global, Free, Meta)
, Elim(..)
, unHead
, global
, free
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
  -- * Patterns
, Pattern(..)
  -- * Modules
, Module(..)
, Def(..)
) where

import           Control.Effect.Empty
import           Data.Bifoldable
import           Data.Bifunctor
import           Data.Bitraversable
import           Data.Foldable (foldl', toList)
import           Data.Functor (void)
import qualified Data.IntMap as IntMap
import           Data.Monoid (First(..))
import           Data.Traversable (mapAccumL)
import qualified Facet.Context as Ctx
import           Facet.Name (CName, Level(..), MName, QName, UName)
import           Facet.Stack
import           Facet.Syntax
import           GHC.Stack

-- Values

-- FIXME: replace products, void, and unit with references to constant datatypes.
-- FIXME: represent closed portions of the tree explicitly?
data Value a
  = Type
  | Void  -- FIXME: 🔥
  | TUnit -- FIXME: 🔥
  | Unit  -- FIXME: 🔥
  | (Pl_ UName ::: Value a) :=> (Value a -> Value a)
  -- FIXME: consider type-indexed patterns & an existential clause wrapper to ensure name & variable patterns have the same static shape
  | Lam (Pl_ UName ::: Value a) (Value a -> Value a)
  -- | Neutral terms are an unreduced head followed by a stack of eliminators.
  | Neut (Head a) (Stack (Elim (Value a)))
  | TPrd (Value a) (Value a) -- FIXME: 🔥
  | Prd (Value a) (Value a)  -- FIXME: 🔥

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
        &&  let b1' = b1 (free n)
                b2' = b2 (free n)
            in go (n + 1) b1' b2'
      (_ :=> _, _) -> False
      (Lam _ b1, Lam _ b2) ->
        let b1' = b1 (free n)
            b2' = b2 (free n)
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
      (App a1, App a2) -> pl a1 == pl a2 && go n (out a1) (out a2)
      (App _, _) -> False
      (Case cs1, Case cs2)
        | length cs1 == length cs2 -> and (zipWith (eqPat n) (toList cs1) (toList cs2))
      (Case _, _) -> False
    eqPat n (p1, b1) (p2, b2)
      =   void p1 == void p2
      &&  let (n', p') = mapAccumL (\ n _ -> (n + 1, free n)) n p2
              b1' = b1 p'
              b2' = b2 p'
          in go n' b1' b2'


data Head a
  = Global (QName ::: Value a) -- ^ Global variables, considered equal by 'QName'.
  | Free a
  | Quote Level
  | Meta (Level ::: Value a) -- ^ Metavariables, considered equal by 'Level'.

instance Eq a => Eq (Head a) where
  Global q1 == Global q2 = tm q1 == tm q2
  Global _  == _         = False
  Free a1   == Free a2   = a1 == a2
  Free _    == _         = False
  Quote l1  == Quote l2  = l1 == l2
  Quote _   == _         = False
  Meta m1   == Meta m2   = tm m1 == tm m2
  Meta _    == _         = False

unHead :: (QName ::: Value a -> b) -> (a -> b) -> (Level -> b) -> (Level ::: Value a -> b) -> Head a -> b
unHead f g h i = \case
  Global n -> f n
  Free   n -> g n
  Quote  n -> h n
  Meta   n -> i n


data Elim a
  = App (Pl_ a) -- FIXME: this is our one codata case; should we generalize this to copattern matching?
  | Case [(Pattern a (UName ::: a), Pattern a a -> a)]


global :: QName ::: Value a -> Value a
global = var . Global

free :: a -> Value a
free = var . Free

quote :: Level -> Value a
quote = var . Quote

metavar :: Level ::: Value a -> Value a
metavar = var . Meta


var :: Head a -> Value a
var = (`Neut` Nil)


unForAll :: Has Empty sig m => Value a -> m (Pl_ UName ::: Value a, Value a -> Value a)
unForAll = \case{ t :=> b -> pure (t, b) ; _ -> empty }

unLam :: Has Empty sig m => Value a -> m (Pl_ UName ::: Value a, Value a -> Value a)
unLam = \case{ Lam n b -> pure (n, b) ; _ -> empty }

unProductT :: Has Empty sig m => Value a -> m (Value a, Value a)
unProductT = \case{ TPrd l r -> pure (l, r) ; _ -> empty }


-- FIXME: how should this work in weak/parametric HOAS?
($$) :: HasCallStack => Value a -> Pl_ (Value a) -> Value a
Neut h es $$ a = Neut h (es :> App a)
(_ :=> b) $$ a = b (out a)
Lam _  b  $$ a = b (out a)
_         $$ _ = error "can’t apply non-neutral/forall type"

infixl 9 $$


case' :: HasCallStack => Value a -> [(Pattern (Value a) (UName ::: Value a), Pattern (Value a) (Value a) -> Value a)] -> Value a
case' (Neut h es) cs = Neut h (es :> Case cs)
case' s           cs = case getFirst (foldMap (\ (p, f) -> First $ f <$> match s p) cs) of
  Just v -> v
  _      -> error "non-exhaustive patterns in lambda"

match :: Value a -> Pattern (Value a) b -> Maybe (Pattern (Value a) (Value a))
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
  pure $ (`substQ` b') . IntMap.singleton (getLevel d)

handleBinderP :: (HasCallStack, Monad m, Traversable t) => Level -> t x -> (t (Value a) -> m (Value a)) -> m (t (Value a) -> Value a)
handleBinderP d p b = do
  let (_, p') = mapAccumL (\ d _ -> (succ d, quote d)) d p
  b' <- b p'
  pure $ \ v -> substQ (snd (foldl' (\ (d, s) v -> (succ d, IntMap.insert (getLevel d) v s)) (d, IntMap.empty) v)) b'

-- FIXME: is it possible to instead perform one complete substitution at the end of <whatever>?
substQ :: HasCallStack => IntMap.IntMap (Value a) -> Value a -> Value a
substQ s = go
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
    Neut f a -> unHead global free (s !) metavar f `elimN` fmap substElim a
    TPrd l r -> TPrd (go l) (go r)
    Prd  l r -> Prd  (go l) (go r)
  substElim = \case
    App a   -> App (fmap go a)
    Case cs -> Case (map (fmap (go .)) cs)
  s ! l = case IntMap.lookup (getLevel l) s of
    Just a  -> a
    Nothing -> quote l

-- | Substitute metavars.
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
    Neut f a -> unHead global free quote (s !) f `elimN` fmap substElim a
    TPrd l r -> TPrd (go l) (go r)
    Prd  l r -> Prd  (go l) (go r)
  substElim = \case
    App a   -> App (fmap go a)
    Case cs -> Case (map (fmap (go .)) cs)
  s ! l = case IntMap.lookup (getLevel (tm l)) s of
    Just a  -> a
    Nothing -> metavar l


newtype AValue = AValue { runAValue :: forall x . Value x }

instance Eq AValue where
  v1 == v2 = (runAValue v1 :: Value Int) == (runAValue v2)


newtype Contextual f = Contextual { runContextual :: forall x . Ctx.Context (Value x ::: Value x) :|-: f x }


-- Patterns

-- FIXME: represent wildcard patterns as var patterns with an empty name.
data Pattern t a
  = Wildcard
  | Var a
  | Con (QName ::: t) [Pattern t a]
  | Tuple [Pattern t a]
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bifoldable Pattern where
  bifoldMap = bifoldMapDefault

instance Bifunctor Pattern where
  bimap = bimapDefault

instance Bitraversable Pattern where
  bitraverse f g = go
    where
    go = \case
      Wildcard -> pure Wildcard
      Var a -> Var <$> g a
      Con (n ::: t) ps -> Con . (n :::) <$> f t <*> traverse go ps
      Tuple ps -> Tuple <$> traverse go ps


-- Modules

data Module a = Module MName [(QName, Def a ::: Value a)]

data Def a
  = DTerm (Value a)
  | DType (Value a)
  | DData [CName ::: Value a]
