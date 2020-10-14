{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core.Value
( Value(..)
, Head(..)
, unHead
, showsPrecValue
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
, shift
, mapValue
, mapValueAll
, join
, AValue(..)
) where

import           Control.Applicative (liftA2)
import           Control.Effect.Empty
import           Control.Monad ((<=<))
import           Data.Foldable (foldl', toList)
import           Data.List (intersperse)
import           Data.Monoid (Ap(..), Endo(..), First(..))
import           Data.Traversable (mapAccumL)
import           Facet.Core.Pattern
import           Facet.Name (Index(..), Level(..), QName, UName, incrLevel, isMeta, levelToIndex, shiftLevel)
import           Facet.Stack hiding ((!))
import qualified Facet.Stack as S
import           Facet.Syntax
import           GHC.Stack
import           Text.Show (showListWith)

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

infixr 0 :=>
infixl 9 :$
infixr 0 :->

data Head a
  = Global QName
  | Local a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

unHead :: (QName -> b) -> (a -> b) -> Head a -> b
unHead f g = \case
  Global n -> f n
  Local  n -> g n


showsPrecValue :: Monad m => Level -> Int -> Value m Level -> m ShowS
showsPrecValue d p = fmap appEndo . go d p
  where
  go d p = \case
    Type     -> lit "Type"
    Void     -> lit "Void"
    TUnit    -> lit "TUnit"
    Unit     -> lit "Unit"
    t :=> b  -> prec 0  $ c (tm t) <+> lit ":::" <+> go d 1 (ty t) <+> lit ":=>" <+> lit "\\ _ ->" <+> (go (incrLevel d) 0 =<< b (bound d))
    TLam n b -> prec 10 $ lit "TLam" <+> c n <+> lit "\\ _ ->" <+> (go (incrLevel d) 11 =<< b (bound d))
    a :-> b  -> prec 0  $ go d 1 a <+> lit ":->" <+> go d 0 b
    Lam    b -> prec 10 $ lit "Lam"  <+> list (traverse (\ (p, b) -> parens True (c p <+> lit ", " <+> lit "\\ _ ->" <+> (go (incrLevel d) 0 =<< b (snd (mapAccumL (\ l _ -> (incrLevel l, bound l)) d p))))) b)
    f :$ as  -> unHead c c f <+> lit ":$" <+> parens True (getAp (foldMap Ap (intersperse (lit ":>") (toList (fmap (go d 0) as)))))
    TPrd l r -> prec 10 $ lit "TPrd" <+> go d 11 l <+> go d 11 r
    Prd  l r -> prec 10 $ lit "Prd"  <+> go d 11 l <+> go d 11 r
    where
    prec d = parens (p > d)
  parens c = fmap (Endo . showParen c . appEndo)
  list = fmap (Endo . showListWith appEndo)
  c :: (Show a, Applicative f) => a -> f (Endo String)
  c = pure . Endo . shows
  lit = pure . Endo . showString
  sp = Endo (showChar ' ')
  a <+> b = liftA2 (\ a b -> a <> sp <> b) a b
  infixl 4 <+>


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


-- | Shift the bound variables in a 'Value' up by a certain amount.
--
-- This should be used when inserting a closed 'Type' at a given 'Level', e.g. when resolving globals.
shift :: Functor m => Level -> Value m Level -> Value m Level
-- FIXME: my kingdom for a 'Functor' instance
-- FIXME: can we make this cheaper by inserting explicit shifts that act as a delta on the level for whatever they contain?
shift d = go
  where
  invd = Level (-getLevel d)
  go = \case
    Type -> Type
    Void -> Void
    TUnit -> TUnit
    Unit -> Unit
    t :=> b -> fmap go t :=> binder b
    a :-> b -> go a :-> go b
    TLam n b -> TLam n (binder b)
    Lam ps -> Lam (map (\ (p, b) -> (p, fmap go . b . fmap (shift invd))) ps)
    f :$ as -> fmap (shiftLevel d) f :$ fmap go as
    TPrd l r -> TPrd (go l) (go r)
    Prd l r -> Prd (go l) (go r)
  -- FIXME: we /probably/ need to invert the shift here? how can we be sure?
  binder b = fmap go . b . shift invd


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
