{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core.Value
( Value(..)
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
, shift
, foldContext
, foldContextAll
) where

import           Control.Applicative (liftA2)
import           Control.Effect.Empty
import           Control.Monad ((<=<))
import           Data.Foldable (foldl', toList)
import           Data.List (intersperse)
import           Data.Monoid (Ap(..), Endo(..))
import           Data.Traversable (mapAccumL)
import           Facet.Context hiding (empty)
import qualified Facet.Context as C
import           Facet.Core.Pattern
import           Facet.Name (Level(..), QName, UName, incrLevel, shiftLevel)
import           Facet.Stack hiding ((!))
import           Facet.Syntax
import           Text.Show (showListWith)
import           GHC.Stack

-- FIXME: eliminate TLam; track type introductions and applications with annotations in the context.
data Value f a
  = Type
  | Void
  | TUnit
  | Unit
  | (UName ::: Value f a) :=> (Value f a -> f (Value f a))
  | TLam UName (Value f a -> f (Value f a))
  | Value f a :-> Value f a
  | Lam UName (Value f a -> f (Value f a))
  | Either QName a :$ Stack (Value f a)
  | TPrd (Value f a) (Value f a)
  | Prd (Value f a) (Value f a)
  -- FIXME: consider type-indexed patterns & an existential clause wrapper to ensure name & variable patterns have the same static shape
  | Case (Value f a) [(Pattern UName, Pattern (Value f a) -> f (Value f a))]

infixr 0 :=>
infixl 9 :$
infixr 0 :->


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
    Lam  n b -> prec 10 $ lit "Lam"  <+> c n <+> lit "\\ _ ->" <+> (go (incrLevel d) 11 =<< b (bound d))
    f :$ as  -> either c c f <+> lit ":$" <+> parens True (getAp (foldMap Ap (intersperse (lit ":>") (toList (fmap (go d 0) as)))))
    TPrd l r -> prec 10 $ lit "TPrd" <+> go d 11 l <+> go d 11 r
    Prd  l r -> prec 10 $ lit "Prd"  <+> go d 11 l <+> go d 11 r
    Case s b -> prec 10 $ lit "Case" <+> go d 11 s <+> list (traverse (\ (p, b) -> parens True (c p <+> lit ", " <+> lit "\\ _ ->" <+> (go (incrLevel d) 0 =<< b (snd (mapAccumL (\ l _ -> (incrLevel l, bound l)) d p))))) b)
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
global n = Left n :$ Nil

bound :: a -> Value f a
bound n = Right n :$ Nil


unForAll :: Has Empty sig m => Value f a -> m (UName ::: Value f a, Value f a -> f (Value f a))
unForAll = \case{ t :=> b -> pure (t, b) ; _ -> empty }

unTLam :: Has Empty sig m => Value f a -> m (UName, Value f a -> f (Value f a))
unTLam = \case{ TLam n b -> pure (n, b) ; _ -> empty }

unArrow :: Has Empty sig m => Value f a -> m (Value f a, Value f a)
unArrow = \case{ a :-> b -> pure (a, b) ; _ -> empty }

unLam :: Has Empty sig m => Value f a -> m (UName, Value f a -> f (Value f a))
unLam = \case{ Lam n b -> pure (n, b) ; _ -> empty }

unProductT :: Has Empty sig m => Value f a -> m (Value f a, Value f a)
unProductT = \case{ TPrd l r -> pure (l, r) ; _ -> empty }


($$) :: (HasCallStack, Applicative f) => Value f a -> Value f a -> f (Value f a)
(f :$ as) $$ a = pure (f :$ (as :> a))
(_ :=> b) $$ a = b a
TLam _ b  $$ a = b a
Lam  _ b  $$ a = b a
_         $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (HasCallStack, Foldable t, Monad f) => Value f a -> t (Value f a) -> f (Value f a)
f $$* as = foldl' (\ f a -> f >>= ($$ a)) (pure f) as

infixl 9 $$, $$*


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
    Lam n b -> Lam n (binder b)
    f :$ as -> fmap (shiftLevel d) f :$ fmap go as
    TPrd l r -> TPrd (go l) (go r)
    Prd l r -> Prd (go l) (go r)
    Case s ps -> Case (go s) (map (\ (p, b) -> (p, fmap go . b . fmap (shift invd))) ps)
  -- FIXME: we /probably/ need to invert the shift here? how can we be sure?
  binder b = fmap go . b . shift invd


foldContext :: (HasCallStack, Monad m) => (Context a -> Level -> a) -> (Value m a -> m a) -> Context a -> Value m Level -> m a
foldContext bd fold env = fold <=< go env
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
    Lam  n b -> pure $ Lam  n $ bind env n b
    f :$ as  -> do
      let f' = either global (bound . bd env) f
      as' <- traverse (go env) as
      f' $$* as'
    TPrd l r -> TPrd <$> go env l <*> go env r
    Prd  l r -> Prd  <$> go env l <*> go env r
    Case s ps -> Case <$> go env s <*> pure (map (\ (p, b) -> (p, bindP env p b)) ps)
  bind env n b = \ v -> do
    b' <- b (bound (level env))
    v' <- fold v
    go (env |> (n ::: v')) b'
  bindP env p b = let names = toList p in names `seq` \ v -> do
    b' <- b (snd (mapAccumL (\ l _ -> (incrLevel l, bound l)) (level env) v))
    v' <- traverse fold v
    go (foldl (|>) env (zipWith (:::) names (toList v'))) b'

foldContextAll :: (HasCallStack, Monad m) => (Context a -> Level -> a) -> (Value m a -> m a) -> Context (Value m Level) -> m (Context a)
foldContextAll bd fold = go . getContext
  where
  go Nil     = pure C.empty
  go (as:>a) = do
    as' <- go as
    a'  <- foldContext bd fold as' (ty a)
    pure $ as' |> (tm a ::: a')
