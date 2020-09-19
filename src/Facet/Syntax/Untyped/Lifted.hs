{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Syntax.Untyped.Lifted
( S.App(..)
, S.Expr(global, unit, (**))
, S.Err(..)
, S.Type(_Type, _Unit, tglobal, (-->), (.*))
, S.Module(..)
, S.Decl((.=))
, S.ForAll
, lam
, lam0
, (>=>)
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


(>=>)
  :: (Applicative m, Permutable env, S.ForAll ty decl)
  => (m :.: env) ty
  -> (forall env' . Permutable env' => (env :.: env') ty -> (m :.: env :.: env') decl)
  -> (m :.: env) decl
t >=> b = (S.>=>) <$> t <*> C (getC <$> getC (b (C (pure id))))

infixr 1 >=>

(>->)
  :: (Applicative m, Permutable env, S.Decl expr ty decl)
  => (m :.: env) ty
  -> (forall env' . Permutable env' => (env :.: env') expr -> (m :.: env :.: env') decl)
  -> (m :.: env) decl
t >-> b = (S.>->) <$> t <*> C (getC <$> getC (b (C (pure id))))

infixr 1 >->
