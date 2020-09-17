{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Expr.Lifted
( lam0
, lam1
) where

import qualified Facet.Expr as Expr
import           Facet.Functor.C
import           Facet.Signature

lam0
  :: (Applicative m, Permutable env, Expr.Expr repr)
  => (forall env' . Permutable env' => (env :.: env') (repr None a) -> (m :.: (env :.: env')) (repr sig b))
  -> (m :.: env) (repr sig (repr sig a -> repr sig b))
lam0 f = Expr.lam0 <$> C (getC <$> getC (f (C (pure id))))

lam1
  :: (Applicative m, Permutable env, Expr.Expr repr)
  => (forall env' . Permutable env' => (env :.: env') (Either (repr None a) (Expr.Inst eff (repr (Sum eff sig) a))) -> (m :.: (env :.: env')) (repr sig b))
  -> (m :.: env) (repr sig (repr (Sum eff sig) a -> repr sig b))
lam1 f = Expr.lam1' <$> C (getC <$> getC (f (C (pure id))))
