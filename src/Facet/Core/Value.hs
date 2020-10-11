{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core.Value
( Value(..)
, showsPrecValue
, Type
, Expr
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

import Control.Applicative (liftA2)
import Control.Effect.Empty
import Control.Monad ((<=<))
import Data.Foldable (foldl', toList)
import Data.List (intersperse)
import Data.Monoid (Ap(..), Endo(..))
import Facet.Name (Level(..), QName, UName, getIndex, incrLevel, levelToIndex, shiftLevel)
import Facet.Stack
import Facet.Syntax
import GHC.Stack

data Value f a
  = Type
  | Void
  | UnitT
  | Unit
  | (UName ::: Value f a) :=> (Value f a -> f (Value f a))
  | TLam UName (Value f a -> f (Value f a))
  | Value f a :-> Value f a
  | Lam UName (Value f a -> f (Value f a))
  | Either QName a :$ Stack (Value f a)
  | TPrd (Value f a) (Value f a)
  | Prd (Value f a) (Value f a)

infixr 0 :=>
infixl 9 :$
infixr 0 :->


showsPrecValue :: Monad m => Level -> Int -> Value m Level -> m ShowS
showsPrecValue d p = fmap appEndo . go d p
  where
  go d p = \case
    Type     -> lit "Type"
    Void     -> lit "Void"
    UnitT    -> lit "UnitT"
    Unit     -> lit "Unit"
    t :=> b  -> prec 0  $ c (tm t) <+> lit ":::" <+> go d 1 (ty t) <+> lit ":=>" <+> lit "\\ _ ->" <+> (go (incrLevel d) 0 =<< b (bound d))
    TLam n b -> prec 10 $ lit "TLam" <+> c n <+> (go (incrLevel d) 11 =<< b (bound d))
    a :-> b  -> prec 0  $ go d 1 a <+> lit ":->" <+> go d 0 b
    Lam  n b -> prec 10 $ lit "Lam"  <+> c n <+> (go (incrLevel d) 11 =<< b (bound d))
    f :$ as  -> either c c f <+> lit ":$" <+> parens True (getAp (foldMap Ap (intersperse (lit ":>") (toList (fmap (go d 0) as)))))
    TPrd l r -> prec 10 $ lit "TPrd" <+> go d 11 l <+> go d 11 r
    Prd  l r -> prec 10 $ lit "Prd"  <+> go d 11 l <+> go d 11 r
    where
    prec d = parens (p > d)
  parens c = fmap (Endo . showParen c . appEndo)
  c :: (Show a, Applicative f) => a -> f (Endo String)
  c = pure . Endo . shows
  lit = pure . Endo . showString
  sp = Endo (showChar ' ')
  a <+> b = liftA2 (\ a b -> a <> sp <> b) a b
  infixl 4 <+>


type Type = Value
type Expr = Value


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
shift d = go
  where
  invd = Level (-getLevel d)
  go = \case
    Type -> Type
    Void -> Void
    UnitT -> UnitT
    Unit -> Unit
    t :=> b -> fmap go t :=> fmap go . b . shift invd -- we /probably/ need to invert the shift here? how can we be sure?
    a :-> b -> go a :-> go b
    TLam n b -> TLam n (fmap go . b . shift invd)
    Lam n b -> Lam n (fmap go . b . shift invd)
    f :$ as -> fmap (shiftLevel d) f :$ fmap go as
    TPrd l r -> TPrd (go l) (go r)
    Prd l r -> Prd (go l) (go r)


foldContext :: (HasCallStack, Monad m) => (Value m a -> m a) -> Stack a -> Value m Level -> m a
foldContext fold env = fold <=< go env
  where
  go env = \case
    Type     -> pure Type
    Void     -> pure Void
    UnitT    -> pure UnitT
    Unit     -> pure Unit
    t :=> b  -> do
      t' <- traverse (go env) t
      pure $ t' :=> \ v -> do
        b' <- b (bound (Level (length env)))
        v' <- fold v
        go (env:>v') b'
    a :-> b  -> (:->) <$> go env a <*> go env b
    TLam n b -> pure $ TLam n $ \ v -> do
      b' <- b (bound (Level (length env)))
      v' <- fold v
      go (env:>v') b'
    Lam  n b -> pure $ Lam  n $ \ v -> do
      b' <- b (bound (Level (length env)))
      v' <- fold v
      go (env:>v') b'
    f :$ as  -> do
      let f' = either global (bound . (env !) . getIndex . levelToIndex (Level (length env))) f
      as' <- traverse (go env) as
      f' $$* as'
    TPrd l r -> TPrd <$> go env l <*> go env r
    Prd  l r -> Prd  <$> go env l <*> go env r

foldContextAll :: (HasCallStack, Monad m) => (Value m a -> m a) -> Stack (Value m Level) -> m (Stack a)
foldContextAll fold = go
  where
  go Nil     = pure Nil
  go (as:>a) = do
    as' <- go as
    a'  <- foldContext fold as' a
    pure $ as' :> a'
