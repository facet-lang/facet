module Facet.Unify
( unifyN
, unifyP
, unify
) where

import Control.Algebra
import Control.Carrier.Empty.Church
import Control.Effect.Reader
import Control.Effect.State
import Control.Effect.Throw
import Control.Effect.Writer
import Facet.Context hiding (empty)
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

-- FIXME: we don’t get good source references during unification
unifyN :: forall m sig . (HasCallStack, Has (Reader ElabContext :+: Reader StaticContext :+: State (Subst PType Kind) :+: Throw Err :+: Writer Usage) sig m) => NType -> NType -> m ()
unifyN t1 t2 = runEmpty (couldNotUnify (HN t1) (HN t2)) pure (unifyN' t1 t2)

unifyP :: forall m sig . (HasCallStack, Has (Reader ElabContext :+: Reader StaticContext :+: State (Subst PType Kind) :+: Throw Err :+: Writer Usage) sig m) => PType -> PType -> m ()
unifyP t1 t2 = runEmpty (couldNotUnify (HP t1) (HP t2)) pure (unifyP' t1 t2)

unify :: (HasCallStack, Has (Reader ElabContext :+: Reader StaticContext :+: State (Subst PType Kind) :+: Throw Err :+: Writer Usage) sig m) => HType -> HType -> m ()
unify t1 t2 = runEmpty (couldNotUnify t1 t2) pure (unify' t1 t2)


unify' :: (HasCallStack, Has (Empty :+: Reader ElabContext :+: Reader StaticContext :+: State (Subst PType Kind) :+: Throw Err :+: Writer Usage) sig m) => HType -> HType -> m ()
unify' t1 t2 = case (t1, t2) of
  (HN n1, HN n2) -> unifyN' n1 n2
  (HN{}, _)      -> empty
  (HP p1, HP p2) -> unifyP' p1 p2
  (HP{}, _)      -> empty
  (HK k1, HK k2) -> unifyK' k1 k2
  (HK{}, _)      -> empty

unifyN' :: (HasCallStack, Has (Empty :+: Reader ElabContext :+: Reader StaticContext :+: State (Subst PType Kind) :+: Throw Err :+: Writer Usage) sig m) => NType -> NType -> m ()
unifyN' t1 t2 = case (t1, t2) of
  (Arrow _ _ a1 b1, Arrow _ _ a2 b2) -> unifyP' a1 a2 >> unifyN' b1 b2
  (Arrow{}, _)                       -> empty
  (Comp s1 t1, Comp s2 t2)           -> unifySig' s1 s2 >> unifyP' t1 t2
  (Comp{}, _)                        -> empty

unifyP' :: (HasCallStack, Has (Empty :+: Reader ElabContext :+: Reader StaticContext :+: State (Subst PType Kind) :+: Throw Err :+: Writer Usage) sig m) => PType -> PType -> m ()
unifyP' t1 t2 = case (t1, t2) of
  (ForAll n t1 b1, ForAll _ t2 b2)           -> unifyK' t1 t2 >> depth >>= \ d -> Binding n zero (SType t1) |- unifyP' (b1 (free d)) (b2 (free d))
  (ForAll{}, _)                              -> empty
  (Ne (Metavar v1) Nil, Ne (Metavar v2) Nil) -> flexFlex v1 v2
  (Ne (Metavar v1) Nil, t2)                  -> solve v1 t2
  (t1, Ne (Metavar v2) Nil)                  -> solve v2 t1
  (Ne v1 sp1, Ne v2 sp2)                     -> var v1 v2 >> spine unifyP' sp1 sp2
  (Ne{}, _)                                  -> empty
  (String, String)                           -> pure ()
  (String, _)                                -> empty
  (Thunk t1, Thunk t2)                       -> unifyN' t1 t2
  (Thunk{}, _)                               -> empty

unifyK' :: Has Empty sig m => Kind -> Kind -> m ()
unifyK' t1 t2 = guard (t1 == t2)

var :: (Has Empty sig m) => Var Meta Level -> Var Meta Level -> m ()
var v1 v2 = case (v1, v2) of
  (Global q1, Global q2)   -> guard (q1 == q2)
  (Global{}, _)            -> empty
  (Free v1, Free v2)       -> guard (v1 == v2)
  (Free{}, _)              -> empty
  (Metavar m1, Metavar m2) -> guard (m1 == m2)
  (Metavar{}, _)           -> empty

spine :: (Foldable t, Zip t, Has Empty sig m) => (a -> b -> m ()) -> t a -> t b -> m ()
spine f sp1 sp2 = guard (length sp1 == length sp2) >> zipWithM_ f sp1 sp2

unifySig' :: (Foldable t, Zip t, Has Empty sig m) => t Interface -> t Interface -> m ()
unifySig' c1 c2 = spine unifyK' (getInterface <$> c1) (getInterface <$> c2)

flexFlex :: (HasCallStack, Has (Empty :+: Reader ElabContext :+: Reader StaticContext :+: State (Subst PType Kind) :+: Throw Err :+: Writer Usage) sig m) => Meta -> Meta -> m ()
flexFlex v1 v2
  | v1 == v2  = pure ()
  | otherwise = do
    (t1, t2) <- gets (\ s -> (lookupMeta @PType @Kind v1 s, lookupMeta v2 s))
    case (t1, t2) of
      (Just t1, Just t2) -> unifyP' (tm t1) (tm t2)
      (Just t1, Nothing) -> unifyP' (metavar v2) (tm t1)
      (Nothing, Just t2) -> unifyP' (metavar v1) (tm t2)
      (Nothing, Nothing) -> solve v1 (metavar v2)

solve :: (HasCallStack, Has (Empty :+: Reader ElabContext :+: Reader StaticContext :+: State (Subst PType Kind) :+: Throw Err :+: Writer Usage) sig m) => Meta -> PType -> m ()
solve v t = do
  d <- depth
  if occursInP v d t then
    mismatch (Right (HP (metavar v))) (HP t) -- FIXME: use a specialized error rather than mismatch
  else
    gets (lookupMeta @PType @Kind v) >>= \case
      Nothing          -> modify (solveMeta @PType @Kind v t)
      Just (t' ::: _T) -> unifyP' t' t
