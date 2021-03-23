module Facet.Unify
( Exp(..)
, Act(..)
, UnifyErrReason(..)
, unify
) where

import Control.Carrier.Reader
import Control.Effect.State
import Control.Effect.Sum
import Control.Effect.Throw
import Control.Effect.Writer
import Control.Monad (unless)
import Facet.Context
import Facet.Core.Type
import Facet.Elab
import Facet.Name
import Facet.Semialign
import Facet.Semiring
import Facet.Snoc
import Facet.Syntax
import Facet.Usage
import GHC.Stack

-- FIXME: we don’t get good source references during unification
unify :: (HasCallStack, Has (Throw Err) sig m) => Exp Type -> Act Type -> Elab m Type
unify t1 t2 = runReader (t1 :=: t2) (unifyType (getExp t1) (getAct t2))

mismatch :: (HasCallStack, Has (Reader ElabContext :+: Reader StaticContext :+: Reader (Exp Type :=: Act Type) :+: State (Subst Type) :+: Throw Err :+: Writer Usage) sig m) => m a
mismatch   = ask >>= \ (t1 :=: t2) -> couldNotUnify          (ST <$> t1) (ST <$> t2)

occurs :: (HasCallStack, Has (Reader ElabContext :+: Reader StaticContext :+: Reader (Exp Type :=: Act Type) :+: State (Subst Type) :+: Throw Err :+: Writer Usage) sig m) => Meta -> Type -> m a
occurs v t = ask >>= \ (t1 :=: t2) -> occursCheckFailure v (ST t) (ST <$> t1) (ST <$> t2)

unifyType :: (HasCallStack, Has (Reader ElabContext :+: Reader StaticContext :+: Reader (Exp Type :=: Act Type) :+: State (Subst Type) :+: Throw Err :+: Writer Usage) sig m) => Type -> Type -> m Type
unifyType = curry $ \case
  (VComp s1 t1, VComp s2 t2)                           -> VComp <$> unifySpine (unifyInterface unifyType) s1 s2 <*> unifyType t1 t2
  (VComp s1 t1, t2)                                    -> VComp s1 <$> unifyType t1 t2
  (t1, VComp s2 t2)                                    -> VComp s2 <$> unifyType t1 t2
  (VNe (Free (Left v1)) Nil, VNe (Free (Left v2)) Nil) -> flexFlex v1 v2
  (VNe (Free (Left v1)) Nil, t2)                       -> solve v1 t2
  (t1, VNe (Free (Left v2)) Nil)                       -> solve v2 t1
  (VForAll _ t1 b1, VForAll n t2 b2)                   -> depth >>= \ d -> evalTExpr =<< mkForAll d n <$> unifyKind t1 t2 <*> (Binding n zero (Left t2) |- unifyType (b1 (free d)) (b2 (free d)))
  (VForAll{}, _)                                       -> mismatch
  (VArrow _ _ a1 b1, VArrow n q a2 b2)                 -> VArrow n q <$> unifyType a1 a2 <*> unifyType b1 b2
  (VArrow{}, _)                                        -> mismatch
  (VNe v1 sp1, VNe v2 sp2)                             -> VNe <$> unifyVar v1 v2 <*> unifySpine unifyType sp1 sp2
  (VNe{}, _)                                           -> mismatch
  (VString, VString)                                   -> pure VString
  (VString, _)                                         -> mismatch
  where
  mkForAll d n k b = TForAll n k (quote (succ d) b)

unifyKind :: Has (Reader ElabContext :+: Reader StaticContext :+: Reader (Exp Type :=: Act Type) :+: State (Subst Type) :+: Throw Err :+: Writer Usage) sig m => Kind -> Kind -> m Kind
unifyKind k1 k2 = if k1 == k2 then pure k2 else mismatch

unifyVar :: (Eq a, Eq b, Has (Reader ElabContext :+: Reader StaticContext :+: Reader (Exp Type :=: Act Type) :+: State (Subst Type) :+: Throw Err :+: Writer Usage) sig m) => Var (Either a b) -> Var (Either a b) -> m (Var (Either a b))
unifyVar v1 v2 = if v1 == v2 then pure v2 else mismatch

unifyInterface :: (HasCallStack, Has (Reader ElabContext :+: Reader StaticContext :+: Reader (Exp Type :=: Act Type) :+: State (Subst Type) :+: Throw Err :+: Writer Usage) sig m) => (a -> b -> m c) -> Interface a -> Interface b -> m (Interface c)
unifyInterface with (Interface h1 sp1) (Interface h2 sp2) = Interface h2 <$ unless (h1 == h2) mismatch <*> unifySpine with sp1 sp2

unifySpine :: (Traversable t, Zip t, Has (Reader ElabContext :+: Reader StaticContext :+: Reader (Exp Type :=: Act Type) :+: State (Subst Type) :+: Throw Err :+: Writer Usage) sig m) => (a -> b -> m c) -> t a -> t b -> m (t c)
unifySpine f sp1 sp2 = unless (length sp1 == length sp2) mismatch >> zipWithM f sp1 sp2

flexFlex :: (HasCallStack, Has (Reader ElabContext :+: Reader StaticContext :+: Reader (Exp Type :=: Act Type) :+: State (Subst Type) :+: Throw Err :+: Writer Usage) sig m) => Meta -> Meta -> m Type
flexFlex v1 v2
  | v1 == v2  = pure (metavar v2)
  | otherwise = gets (\ s -> (lookupMeta v1 s, lookupMeta v2 s)) >>= \case
    (Just t1, Just t2) -> unifyType (tm t1) (tm t2)
    (Just t1, Nothing) -> unifyType (metavar v2) (tm t1)
    (Nothing, Just t2) -> unifyType (metavar v1) (tm t2)
    (Nothing, Nothing) -> solve v1 (metavar v2)

solve :: (HasCallStack, Has (Reader ElabContext :+: Reader StaticContext :+: Reader (Exp Type :=: Act Type) :+: State (Subst Type) :+: Throw Err :+: Writer Usage) sig m) => Meta -> Type -> m Type
solve v t = do
  d <- depth
  if occursIn (== Free (Left v)) d t then
    occurs v t
  else
    gets (lookupMeta v) >>= \case
      Nothing          -> t <$ modify (solveMeta v t)
      Just (t' ::: _T) -> unifyType t' t >>= \ t'' -> t'' <$ modify (solveMeta v t'')