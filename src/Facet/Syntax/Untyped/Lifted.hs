{-# LANGUAGE RankNTypes #-}
module Facet.Syntax.Untyped.Lifted
( S.Name
, S.App(..)
, S.Global(..)
, S.Expr(unit, (**))
, S.Err(..)
, S.Type(_Type, _Unit, (-->), (.*))
, S.Module(..)
, S.Decl((.=))
, S.ForAll
, lam
, lam0
, (>=>)
, (>->)
, Permutable
, weaken
) where

import           Control.Applicative (liftA2)
import           Facet.Functor.C
import qualified Facet.Syntax.Untyped as S

lam
  :: (Applicative m, Permutable env, S.Expr repr)
  => (forall env' . Extends env env' => env' (Either repr (repr, repr -> repr)) -> m (env' repr))
  -> m (env repr)
lam f = fmap S.lam . getC <$> f (C (pure id))

lam0
  :: (Applicative m, Permutable env, S.Expr repr)
  => (forall env' . Extends env env' => env' repr -> m (env' repr))
  -> m (env repr)
lam0 f = fmap S.lam0 . getC <$> f (C (pure id))


(>=>)
  :: (Applicative m, Permutable env, S.ForAll ty decl)
  => m (env ty)
  -> (forall env' . Extends env env' => env' ty -> m (env' decl))
  -> m (env decl)
t >=> b = liftA2 (S.>=>) <$> t <*> (getC <$> b (C (pure id)))

infixr 1 >=>

(>->)
  :: (Applicative m, Permutable env, S.Decl expr ty decl)
  => m (env ty)
  -> (forall env' . Extends env env' => env' expr -> m (env' decl))
  -> m (env decl)
t >-> b = liftA2 (S.>->) <$> t <*> (getC <$> b (C (pure id)))

infixr 1 >->
