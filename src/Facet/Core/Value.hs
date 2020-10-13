{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
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
, foldContext
, foldContextAll
, close
, join
) where

import           Control.Applicative (liftA2)
import           Control.Effect.Empty
import           Control.Monad ((<=<))
import           Data.Foldable (foldl', toList)
import           Data.List (intersperse)
import           Data.Monoid (Ap(..), Endo(..), First(..))
import           Data.Traversable (mapAccumL)
import           Facet.Context hiding (empty)
import qualified Facet.Context as C
import           Facet.Core.Pattern
import           Facet.Name (Level(..), QName, UName, incrLevel, levelToIndex, shiftLevel)
import           Facet.Stack hiding ((!))
import           Facet.Syntax
import           GHC.Stack
import           Text.Show (showListWith)

-- FIXME: eliminate TLam; track type introductions and applications with annotations in the context.
-- FIXME: replace :-> with syntax sugar for :=>.
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


foldContext :: (HasCallStack, Monad m) => (Metacontext a -> Context a -> Level -> a) -> (Value m a -> m a) -> Metacontext a -> Context a -> Value m Level -> m a
foldContext bd fold mctx env = fold <=< go env
  where
  go env = \case
    Type     -> pure Type
    Void     -> pure Void
    TUnit    -> pure TUnit
    Unit     -> pure Unit
    t :=> b  -> do
      t' <- traverse (go env) t
      pure $ t' :=> bind env (tm t') b
    a :-> b  -> (:->) <$> go env a <*> go env b
    TLam n b -> pure $ TLam n $ bind env n b
    Lam  ps  -> pure $ Lam $ map (\ (p, b) -> (p, bindP env p b)) ps
    f :$ as  -> do
      let f' = unHead global (bound . bd mctx env) f
      as' <- traverse (go env) as
      f' $$* as'
    TPrd l r -> TPrd <$> go env l <*> go env r
    Prd  l r -> Prd  <$> go env l <*> go env r
  bind env n b = \ v -> do
    b' <- b (bound (level env))
    v' <- fold v
    go (env |> (n ::: v')) b'
  bindP env p b = let names = toList p in names `seq` \ v -> do
    b' <- b (snd (mapAccumL (\ l _ -> (incrLevel l, bound l)) (level env) v))
    v' <- traverse fold v
    go (foldl (|>) env (zipWith (:::) names (toList v'))) b'

-- FIXME: we don’t extend the context & metacontext the way the algebra would (if it would at all). hence, the algebra _can’t_ make a consistently correct decision about what to print, leading to it e.g. sometimes printing types and sometimes printing names, showing quantifiers starting from the wrong level, etc.
foldContextAll :: (HasCallStack, Monad m) => (Metacontext a -> Context a -> Level -> a) -> (Value m a -> m a) -> Metacontext (Value m Level) -> Context (Value m Level) -> m (Metacontext a, Context a)
foldContextAll bd fold mctx ctx = go (elems ctx)
  where
  metas []     = pure (Metacontext [])
  metas (m:ms) = do
    ms' <- metas ms
    m'  <- foldContext bd fold ms' C.empty (ty m)
    pure $ (tm m ::: m') <| ms'
  go Nil     = do
    mctx' <- metas (getMetacontext mctx)
    pure (mctx', C.empty)
  go (as:>a) = do
    (mctx', as') <- go as
    a' <- foldContext bd fold mctx' as' (ty a)
    pure (mctx', as' |> (tm a ::: a'))


close :: (HasCallStack, Monad m) => Metacontext (Value m a) -> Context (Value m a) -> Value m Level -> m (Value m a)
close mctx = go
  where
  go ctx = \case
    Type     -> pure Type
    Void     -> pure Void
    TUnit    -> pure TUnit
    Unit     -> pure Unit
    t :=> b  -> do
      t' <- traverse (go ctx) t
      pure $ t' :=> bind ctx (tm t') b
    a :-> b  -> (:->) <$> go ctx a <*> go ctx b
    TLam n b -> pure $ TLam n $ bind ctx n b
    Lam  ps  -> pure $ Lam $ map (\ (p, b) -> (p, bindP ctx p b)) ps
    f :$ as  -> do
      let f' = unHead global (ty . lookupIn ctx) f
      as' <- traverse (go ctx) as
      f' $$* as'
    TPrd l r -> TPrd <$> go ctx l <*> go ctx r
    Prd  l r -> Prd  <$> go ctx l <*> go ctx r
  bind ctx n b = \ v -> do
    b' <- b (bound (level ctx))
    go (ctx |> (n ::: v)) b'
  bindP ctx p b = let names = toList p in names `seq` \ v -> do
    b' <- b (snd (mapAccumL (\ l _ -> (incrLevel l, bound l)) (level ctx) v))
    go (foldl (|>) ctx (zipWith (:::) names (toList v))) b'
  -- FIXME: lookup in the metacontext.
  lookupIn ctx l = ctx ! levelToIndex (level ctx) l


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
