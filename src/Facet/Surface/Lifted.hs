{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Surface.Lifted
( S.EName(..)
, S.TName(..)
, S.DName(..)
, S.Expr(global, unit, (**), ($$))
, S.Type(tglobal, _Type, _Unit, (-->), (.*), (.$))
, S.Module(..)
, S.Decl((.=))
, S.ForAll
, S.Located(..)
, (S.:::)(..)
, lam
, lam0
, (>~>)
, (>=>)
, (>->)
  -- * Re-exports
, Extends
, (>>>)
, castF
, refl
, strengthen
) where

import           Control.Applicative (liftA2)
import           Facet.Env (Extends, castF, liftBinder, refl, strengthen, (>>>))
import qualified Facet.Surface as S

lam
  :: (Applicative m, Applicative env, S.Expr repr)
  => m (env S.EName)
  -> (forall env' . Applicative env' => Extends env env' -> env' (Either repr (repr, repr -> repr)) -> m (env' repr))
  -> m (env repr)
lam n f = liftA2 S.lam <$> n <*> liftBinder f

lam0
  :: (Applicative m, Applicative env, S.Expr repr)
  => m (env S.EName)
  -> (forall env' . Applicative env' => Extends env env' -> env' repr -> m (env' repr))
  -> m (env repr)
lam0 n f = liftA2 S.lam0 <$> n <*> liftBinder f


(>~>)
  :: (Applicative m, Applicative env, S.Type ty)
  => m (env (S.TName S.::: ty))
  -> (forall env' . Applicative env' => Extends env env' -> env' ty -> m (env' ty))
  -> m (env ty)
t >~> b = liftA2 (S.>~>) <$> t <*> liftBinder b

infixr 1 >~>

(>=>)
  :: (Applicative m, Applicative env, S.ForAll ty decl)
  => m (env (S.TName S.::: ty))
  -> (forall env' . Applicative env' => Extends env env' -> env' ty -> m (env' decl))
  -> m (env decl)
t >=> b = liftA2 (S.>=>) <$> t <*> liftBinder b

infixr 1 >=>

(>->)
  :: (Applicative m, Applicative env, S.Decl expr ty decl)
  => m (env (S.EName S.::: ty))
  -> (forall env' . Applicative env' => Extends env env' -> env' expr -> m (env' decl))
  -> m (env decl)
t >-> b = liftA2 (S.>->) <$> t <*> liftBinder b

infixr 1 >->
