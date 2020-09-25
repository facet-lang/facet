{-# LANGUAGE RankNTypes #-}
module Facet.Syntax.Typed.Lifted
( lam
, lam0
, Expr.Expr
) where

import           Facet.Env
import           Facet.Signature
import qualified Facet.Syntax.Typed as Expr

lam
  :: (Applicative m, Applicative env, Expr.Expr repr)
  => (forall env' . Applicative env' => Extends env env' -> env' (Either (repr None a) (Expr.Inst eff (repr (Sum eff sig) a))) -> m (env' (repr sig b)))
  -> m (env (repr sig (repr (Sum eff sig) a -> repr sig b)))
lam f = fmap Expr.lam <$> liftBinder f

lam0
  :: (Applicative m, Applicative env, Expr.Expr repr)
  => (forall env' . Applicative env' => Extends env env' -> env' (repr None a) -> m (env' (repr sig b)))
  -> m (env (repr sig (repr sig a -> repr sig b)))
lam0 f = fmap (fmap (. Expr.weakenBy InR)) <$> lam (\ env -> f env . fmap (either Expr.val Expr.absurdI))
