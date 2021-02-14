{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Eval
( -- * Evaluation
  eval
  -- * Machinery
, Op(..)
, Handler
, runEval
, Eval(..)
  -- * Values
, Value(..)
, unit
  -- * Quotation
, quoteV
) where

import Control.Algebra hiding (Handler)
import Control.Applicative (Alternative(..))
import Control.Effect.Reader
import Control.Monad (ap, foldM, guard, liftM, (<=<))
import Control.Monad.Trans.Class
import Data.Either (partitionEithers)
import Data.Foldable (foldl')
import Data.Function
import Data.Semialign.Exts (zipWithM)
import Data.Text (Text)
import Data.Void (Void)
import Facet.Core.Module
import Facet.Core.Term
import Facet.Graph
import Facet.Name hiding (Op)
import Facet.Stack
import Facet.Syntax
import GHC.Stack (HasCallStack)
import Prelude hiding (zipWith)

eval :: forall m sig . (HasCallStack, Has (Reader Graph :+: Reader Module) sig m) => Expr -> Eval m (Value (Eval m))
eval = force <=< go
  where
  go = \case
    XVar (Global n)  -> pure $ VNe (Global n) Nil
    XVar (Free v)    -> lookupEnv v
    XVar (Metavar m) -> case m of {}
    XTLam b          -> go b
    XInst f _        -> go f
    XLam cs          -> pure $ VLam
      (map fst cs)
      (\ toph op k -> foldr (\ (p, b) rest -> maybe rest (b . fmap pure . PEff) (matchE p op k)) (toph op k) es)
      -- FIXME: forcing in the closure’s environment instead of the caller’s is almost certainly wrong
      (\ v -> foldr (\ (p, b) rest -> maybe rest (b . fmap pure . PVal) (matchV p v)) (error "non-exhaustive patterns in lambda") vs)
      where
      cs' = map (\ (p, e) -> (p, foldr bind (go e))) cs
      (es, vs) = partitionEithers (map (\case{ (PEff e, b) -> Left (e, b) ; (PVal v, b) -> Right (v, b) }) cs')
    XApp  f a        -> go f >>= \ f' -> app f' (go a)
    XThunk b         -> pure $ VThunk (go b)
    XForce t         -> go t >>= \ t' -> app t' (pure unit)
    XCon n _ fs      -> VCon n <$> traverse go fs
    XString s        -> pure $ VString s
    XOp n _ sp       -> do
      sp' <- traverse go sp
      Eval $ \ env h k -> runEval env h k (h (Op n sp') pure)
  app f a = case f of
    VNe h sp   -> pure $ VNe h (sp:>a)
    VLam _ h k -> extendHandler h (a >>= force) >>= k
    _          -> error "throw a real error (apply)"
  force = \case
    VNe n sp -> forceN n sp
    v        -> pure v
  forceN (Global n)  sp = forceGlobal n sp
  forceN (Free n)    sp = pure $ VNe (Free n) sp
  forceN (Metavar m) _  = case m of {}
  forceGlobal n sp = do
    mod <- lift ask
    graph <- lift ask
    case lookupQ graph mod n of
      Just (_ :=: Just (DTerm v) ::: _) -> do
        v' <- go v
        force =<< foldM app v' sp
      _                                 -> error "throw a real error here"

extendHandler :: (Handler (Eval m) -> Handler (Eval m)) -> Eval m a -> Eval m a
extendHandler ext (Eval run) = Eval $ \ env h -> run env (ext h)

lookupEnv :: Index -> Eval m (Value (Eval m))
lookupEnv (Index i) = Eval $ \ env h k -> runEval env h k (env ! i)

bind :: Eval m (Value (Eval m)) -> Eval m a -> Eval m a
bind a (Eval run) = Eval $ \ env h k -> run (env :> a) h k


-- Machinery

data Op a = Op (Q Name) (Stack a)

type Handler m = Op (Value m) -> (Value m -> m (Value m)) -> m (Value m)

type Env m = Stack (m (Value m))

runEval :: Env (Eval m) -> Handler (Eval m) -> (a -> m r) -> Eval m a -> m r
runEval env hdl k (Eval m) = m env hdl k

newtype Eval m a = Eval (forall r . Env (Eval m) -> Handler (Eval m) -> (a -> m r) -> m r)

instance Functor (Eval m) where
  fmap = liftM

instance Applicative (Eval m) where
  pure a = Eval $ \ _ _ k -> k a
  (<*>) = ap

instance Monad (Eval m) where
  m >>= f = Eval $ \ env hdl k -> runEval env hdl (runEval env hdl k . f) m

instance MonadTrans Eval where
  lift m = Eval $ \ _ _ k -> m >>= k

instance Algebra sig m => Algebra sig (Eval m) where
  alg hdl sig ctx = Eval $ \ env h k -> alg (runEval env h pure . hdl) sig ctx >>= k


-- Values

data Value m
  = VLam [Pattern Name] (Handler m -> Handler m) (Value m -> m (Value m))
  | VNe (Var Void Level) (Stack (m (Value m)))
  -- fixme: should we represent thunks & forcing explicitly?
  | VThunk (m (Value m))
  -- fixme: should these be computations too?
  | VOp (Op (Value m)) (Value m)
  | VCon (Q Name) (Stack (Value m))
  | VString Text

free :: Level -> Value m
free v = VNe (Free v) Nil

unit :: Value m
unit = VCon (["Data", "Unit"] :.: U "unit") Nil


-- Elimination

matchE :: EffectPattern Name -> Op (Value m) -> (Value m -> m (Value m)) -> Maybe (EffectPattern (Value m))
matchE (POp n ps _) (Op n' fs) k = POp n' <$ guard (n == n') <*> zipWithM matchV ps fs <*> pure (VLam [PVal (PVar __)] id k)

matchV :: ValuePattern Name -> Value m -> Maybe (ValuePattern (Value m))
matchV p s = case p of
  PWildcard -> pure PWildcard
  PVar _    -> pure (PVar s)
  PCon n ps
    | VCon n' fs <- s -> PCon n' <$ guard (n == n') <*> zipWithM matchV ps fs
  PCon{}    -> empty


-- Quotation

quoteV :: Monad m => Level -> Value m -> m Expr
quoteV d = \case
  VLam ps h k     -> XLam <$> traverse (quoteClause d h k) ps
  VThunk b        -> XThunk <$> (quoteV d =<< b)
  VNe h sp        -> foldl' XApp (XVar (levelToIndex d <$> h)) <$> traverse (quoteV d =<<) sp
  VOp (Op q fs) k -> XApp <$> quoteV d k <*> (XOp q Nil <$> traverse (quoteV d) fs)
  VCon n fs       -> XCon n Nil <$> traverse (quoteV d) fs
  VString s       -> pure $ XString s

quoteClause :: Monad m => Level -> (Handler m -> Handler m) -> (Value m -> m (Value m)) -> Pattern Name -> m (Pattern Name, Expr)
quoteClause d h k p = fmap (p,) . quoteV d' =<< case p' of
  PVal p'           -> k (constructV p')
  PEff (POp q fs k) -> h (\ op _ -> pure (VOp op k)) (Op q (constructV <$> fs)) pure
  where
  (d', p') = fill ((,) <$> succ <*> free) d p


constructV :: ValuePattern (Value m) -> Value m
constructV = \case
  PWildcard -> unit -- FIXME: maybe should provide a variable here anyway?
  PVar v    -> v
  PCon q fs -> VCon q (constructV <$> fs)
