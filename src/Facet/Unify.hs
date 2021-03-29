{-# LANGUAGE ImplicitParams #-}
module Facet.Unify
( -- * Unification
  Exp(..)
, Act(..)
, UnifyErrReason(..)
, unify
  -- * Equating
, runEq
, eqInterface
) where

import Control.Carrier.Empty.Church
import Control.Carrier.Error.Church
import Control.Effect.Reader
import Control.Effect.State
import Control.Effect.Sum
import Control.Effect.Writer
import Control.Monad (unless)
import Facet.Core.Pattern
import Facet.Core.Type
import Facet.Elab
import Facet.Name
import Facet.Semialign
import Facet.Semiring
import Facet.Snoc
import Facet.Subst
import Facet.Syntax
import Facet.Usage
import GHC.Stack

-- Unification

-- FIXME: we don’t get good source references during unification
unify :: (HasCallStack, Has (Throw Err) sig m) => Exp Type -> Act Type -> Elab m Type
unify t1 t2 = runUnify t1 t2 (unifyType (getExp t1) (getAct t2))

runUnify :: Has (Throw Err) sig m => Exp Type -> Act Type -> ErrorC (WithCallStack UnifyErrReason) (Elab m) a -> Elab m a
runUnify t1 t2 = runError (withCallStack (\ r -> err (Unify r (Right . CT <$> t1) (CT <$> t2)))) pure

mismatch :: (HasCallStack, Has (Reader ElabContext :+: Reader StaticContext :+: State (Subst Type) :+: Throw Err :+: Throw (WithCallStack UnifyErrReason) :+: Writer Usage) sig m) => m a
mismatch   = withFrozenCallStack $ throwError $ WithCallStack GHC.Stack.callStack Mismatch

occurs :: (HasCallStack, Has (Reader ElabContext :+: Reader StaticContext :+: State (Subst Type) :+: Throw Err :+: Throw (WithCallStack UnifyErrReason) :+: Writer Usage) sig m) => Meta -> Type -> m a
occurs v t = withFrozenCallStack $ throwError $ WithCallStack GHC.Stack.callStack  (Occurs v (CT t))

unifyType :: (HasCallStack, Has (Reader ElabContext :+: Reader StaticContext :+: State (Subst Type) :+: Throw Err :+: Throw (WithCallStack UnifyErrReason) :+: Writer Usage) sig m) => Type -> Type -> m Type
unifyType = curry $ \case
  (VComp s1 t1, VComp s2 t2)                           -> VComp . fromInterfaces <$> unifySpine unifyInterface (interfaces s1) (interfaces s2) <*> unifyType t1 t2
  (VComp s1 t1, t2)                                    -> VComp s1 <$> unifyType t1 t2
  (t1, VComp s2 t2)                                    -> VComp s2 <$> unifyType t1 t2
  (VNe (Free (Left v1)) Nil, VNe (Free (Left v2)) Nil) -> flexFlex v1 v2
  (VNe (Free (Left v1)) Nil, t2)                       -> solve v1 t2
  (t1, VNe (Free (Left v2)) Nil)                       -> solve v2 t1
  (VForAll _ t1 b1, VForAll n t2 b2)                   -> depth >>= \ d -> evalTExpr =<< mkForAll d n <$> unifyKind t1 t2 <*> ((zero, pvar (n ::: CK t2)) |- unifyType (b1 (free (LName d n))) (b2 (free (LName d n))))
  (VForAll{}, _)                                       -> mismatch
  (VArrow _ _ a1 b1, VArrow n q a2 b2)                 -> VArrow n q <$> unifyType a1 a2 <*> unifyType b1 b2
  (VArrow{}, _)                                        -> mismatch
  (VNe v1 sp1, VNe v2 sp2)                             -> VNe <$> unifyVar v1 v2 <*> unifySpine unifyType sp1 sp2
  (VNe{}, _)                                           -> mismatch
  (VString, VString)                                   -> pure VString
  (VString, _)                                         -> mismatch
  where
  mkForAll d n k b = TForAll n k (quote (succ d) b)

unifyKind :: Has (Reader ElabContext :+: Reader StaticContext :+: State (Subst Type) :+: Throw Err :+: Throw (WithCallStack UnifyErrReason) :+: Writer Usage) sig m => Kind -> Kind -> m Kind
unifyKind k1 k2 = if k1 == k2 then pure k2 else mismatch

unifyVar :: (Eq a, Eq b, HasCallStack, Has (Reader ElabContext :+: Reader StaticContext :+: State (Subst Type) :+: Throw Err :+: Throw (WithCallStack UnifyErrReason) :+: Writer Usage) sig m) => Var (Either a b) -> Var (Either a b) -> m (Var (Either a b))
unifyVar v1 v2 = if v1 == v2 then pure v2 else mismatch

unifyInterface :: (HasCallStack, Has (Reader ElabContext :+: Reader StaticContext :+: State (Subst Type) :+: Throw Err :+: Throw (WithCallStack UnifyErrReason) :+: Writer Usage) sig m) => Interface Type -> Interface Type -> m (Interface Type)
unifyInterface (Interface h1 sp1) (Interface h2 sp2) = Interface h2 <$ unless (h1 == h2) mismatch <*> unifySpine unifyType sp1 sp2

unifySpine :: (Traversable t, Zip t, Has (Reader ElabContext :+: Reader StaticContext :+: State (Subst Type) :+: Throw Err :+: Throw (WithCallStack UnifyErrReason) :+: Writer Usage) sig m) => (a -> b -> m c) -> t a -> t b -> m (t c)
unifySpine f sp1 sp2 = unless (length sp1 == length sp2) mismatch >> zipWithM f sp1 sp2

flexFlex :: (HasCallStack, Has (Reader ElabContext :+: Reader StaticContext :+: State (Subst Type) :+: Throw Err :+: Throw (WithCallStack UnifyErrReason) :+: Writer Usage) sig m) => Meta -> Meta -> m Type
flexFlex v1 v2
  | v1 == v2  = pure (metavar v2)
  | otherwise = gets (\ s -> (lookupMeta v1 s, lookupMeta v2 s)) >>= \case
    (Just t1, Just t2) -> unifyType t1 t2
    (Just t1, Nothing) -> unifyType (metavar v2) t1
    (Nothing, Just t2) -> unifyType (metavar v1) t2
    (Nothing, Nothing) -> solve v1 (metavar v2)

solve :: (HasCallStack, Has (Reader ElabContext :+: Reader StaticContext :+: State (Subst Type) :+: Throw Err :+: Throw (WithCallStack UnifyErrReason) :+: Writer Usage) sig m) => Meta -> Type -> m Type
solve v t = do
  d <- depth
  if occursIn v d t then
    occurs v t
  else
    gets (lookupMeta v) >>= \case
      Nothing -> t <$ modify (solveMeta v t)
      Just t' -> unifyType t' t >>= \ t'' -> t'' <$ modify (solveMeta v t'')


-- Equating

runEq :: Applicative m => EmptyC m () -> m Bool
runEq = execEmpty

eqType :: (HasCallStack, Has (Empty :+: Reader ElabContext :+: Reader StaticContext :+: State (Subst Type) :+: Throw Err :+: Writer Usage) sig m) => Type -> Type -> m ()
eqType = curry $ \case
  (VComp s1 t1, VComp s2 t2)           -> eqSpine eqInterface (interfaces s1) (interfaces s2) *> eqType t1 t2
  (VComp _ t1, t2)                     -> eqType t1 t2
  (t1, VComp _ t2)                     -> eqType t1 t2
  (VForAll _ t1 b1, VForAll n t2 b2)   -> depth >>= \ d -> guard (t1 == t2) *> ((zero, pvar (n ::: CK t2)) |- eqType (b1 (free (LName d n))) (b2 (free (LName d n))))
  (VForAll{}, _)                       -> empty
  (VArrow _ _ a1 b1, VArrow _ _ a2 b2) -> eqType a1 a2 *> eqType b1 b2
  (VArrow{}, _)                        -> empty
  (VNe v1 sp1, VNe v2 sp2)             -> guard (v1 == v2) *> eqSpine eqType sp1 sp2
  (VNe{}, _)                           -> empty
  (VString, VString)                   -> pure ()
  (VString, _)                         -> empty

eqInterface :: (HasCallStack, Has (Empty :+: Reader ElabContext :+: Reader StaticContext :+: State (Subst Type) :+: Throw Err :+: Writer Usage) sig m) => Interface Type -> Interface Type -> m ()
eqInterface (Interface h1 sp1) (Interface h2 sp2) = guard (h1 == h2) *> eqSpine eqType sp1 sp2

eqSpine :: (Foldable t, Zip t, Has Empty sig m) => (a -> b -> m ()) -> t a -> t b -> m ()
eqSpine f sp1 sp2 = guard (length sp1 == length sp2) *> zipWithM_ f sp1 sp2


-- Callstacks

data WithCallStack a = WithCallStack CallStack a

withCallStack :: (HasCallStack => a -> b) -> WithCallStack a -> b
withCallStack f (WithCallStack callStack a) = let ?callStack = callStack in f a
