{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Syntax.Untyped.Lifted
( S.Expr(global, unit, ($$), (**))
, S.Err(..)
, S.Type(_Type, _Unit, tglobal, (-->), (.*), (.$))
, S.Module(..)
, lam
, lam0
, (>->)
) where

import           Facet.Functor.C
import qualified Facet.Syntax.Untyped as S

lam
  :: (Applicative m, Permutable env, S.Expr repr)
  => (forall env' . Permutable env' => (env :.: env') (Either repr (repr, repr -> repr)) -> (m :.: env :.: env') repr)
  -> (m :.: env) repr
lam f = S.lam <$> C (getC <$> getC (f (C (pure id))))

lam0
  :: (Applicative m, Permutable env, S.Expr repr)
  => (forall env' . Permutable env' => (env :.: env') repr -> (m :.: env :.: env') repr)
  -> (m :.: env) repr
lam0 f = S.lam0 <$> C (getC <$> getC (f (C (pure id))))


(>->)
  :: (Applicative m, Permutable env, S.Type ty)
  => (m :.: env) ty
  -> (forall env' . Permutable env' => (env :.: env') ty -> (m :.: env :.: env') ty)
  -> (m :.: env) ty
t >-> b = (S.>->) <$> t <*> C (getC <$> getC (b (C (pure id))))

infixr 1 >->
