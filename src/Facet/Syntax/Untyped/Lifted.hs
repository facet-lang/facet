{-# LANGUAGE RankNTypes #-}
module Facet.Syntax.Untyped.Lifted
( S.Name
, S.Global(..)
, S.Expr(unit, (**), ($$))
, S.Type(_Type, _Unit, (-->), (.*), (.$))
, S.Module(..)
, S.Decl((.=))
, S.ForAll
, lam
, lam0
, (>=>)
, (>->)
) where

import           Control.Applicative (liftA2)
import qualified Facet.Env as E
import qualified Facet.Syntax.Untyped as S

lam
  :: (Applicative m, Applicative env, S.Expr repr)
  => (forall env' . Applicative env' => E.Extends env env' -> env' (Either repr (repr, repr -> repr)) -> m (env' repr))
  -> m (env repr)
lam f = fmap S.lam <$> E.liftBinder f

lam0
  :: (Applicative m, Applicative env, S.Expr repr)
  => (forall env' . Applicative env' => E.Extends env env' -> env' repr -> m (env' repr))
  -> m (env repr)
lam0 f = fmap S.lam0 <$> E.liftBinder f


(>=>)
  :: (Applicative m, Applicative env, S.ForAll ty decl)
  => m (env ty)
  -> (forall env' . Applicative env' => E.Extends env env' -> env' ty -> m (env' decl))
  -> m (env decl)
t >=> b = liftA2 (S.>=>) <$> t <*> E.liftBinder b

infixr 1 >=>

(>->)
  :: (Applicative m, Applicative env, S.Decl expr ty decl)
  => m (env ty)
  -> (forall env' . Applicative env' => E.Extends env env' -> env' expr -> m (env' decl))
  -> m (env decl)
t >-> b = liftA2 (S.>->) <$> t <*> E.liftBinder b

infixr 1 >->
