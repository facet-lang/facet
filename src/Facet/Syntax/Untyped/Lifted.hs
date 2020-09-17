{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Syntax.Untyped.Lifted
( Expr.Expr
, lam
, lam0
, ($$)
) where

import           Control.Applicative (liftA2)
import           Facet.Functor.C
import qualified Facet.Syntax.Untyped as Expr

lam
  :: (Applicative m, Permutable env, Expr.Expr repr)
  => (forall env' . Permutable env' => (env :.: env') (Either repr (repr, repr -> repr)) -> (m :.: (env :.: env')) repr)
  -> (m :.: env) repr
lam f = Expr.lam <$> C (getC <$> getC (f (C (pure id))))

lam0
  :: (Applicative m, Permutable env, Expr.Expr repr)
  => (forall env' . Permutable env' => (env :.: env') repr -> (m :.: (env :.: env')) repr)
  -> (m :.: env) repr
lam0 f = Expr.lam0 <$> C (getC <$> getC (f (C (pure id))))

($$) :: (Applicative m, Applicative env, Expr.Expr expr) => m (env expr) -> m (env expr) -> m (env expr)
f $$ a = liftA2 (liftA2 (Expr.$$)) f a

infixl 9 $$
