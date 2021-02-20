{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Eval
( -- * Evaluation
  eval
, evalV'
, evalC'
  -- * Machinery
, Handler
, runEval
, Eval(..)
  -- * Values
, Value(..)
, unit
, Comp(..)
  -- * Quotation
, quoteV
, quoteC
) where

import Control.Algebra hiding (Handler)
import Control.Applicative (Alternative(..))
import Control.Carrier.Reader
import Control.Effect.NonDet (foldMapA)
import Control.Monad (ap, guard, liftM)
import Control.Monad.Trans.Class
import Data.Either (partitionEithers)
import Data.Foldable (foldl')
import Data.Function
import Data.Maybe (fromMaybe)
import Data.Semialign.Exts (zipWithM)
import Data.Text (Text)
import Facet.Core.Module
import Facet.Core.Term
import Facet.Graph
import Facet.Name hiding (Op)
import Facet.Snoc
import Facet.Syntax
import GHC.Stack (HasCallStack)
import Prelude hiding (zipWith)

eval :: forall m sig . (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Expr -> Eval m (Comp (Eval m))
eval = runReader Nil . evalC

evalC :: (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Expr -> EnvC m (Comp (Eval m))
evalC e = case e of
  XTLam b    -> evalC b
  XInst f _  -> evalC f
  XLam cs    -> lam (fmap evalC <$> cs)
  XApp  f a  -> evalC f $$ evalV a
  XOp n _ sp -> op n (evalV <$> sp)
  XVar{}     -> return
  XCon{}     -> return
  XString{}  -> return
  where
  return = lift . creturn =<< evalV e

evalV :: (Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Expr -> EnvC m (Value (Eval m))
evalV e = case e of
  XVar (Global n)  -> evalV =<< global n
  XVar (Free v)    -> var v
  XVar (Metavar m) -> case m of {}
  XCon n _ fs      -> VCon n <$> traverse evalV fs
  XString s        -> pure $ VString s
  XTLam{}          -> thunk
  XInst{}          -> thunk
  XLam{}           -> thunk
  XApp{}           -> thunk
  XOp{}            -> thunk
  where
  thunk = vthunk <$> evalC e

evalC' :: (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Expr' C -> EnvC m (Comp (Eval m))
evalC' = \case
  EXTLam b    -> evalC' b
  EXInst f _  -> evalC' f
  EXLam cs    -> lam (fmap evalC' <$> cs)
  EXApp  f a  -> evalC' f $$ evalV' a
  EXOp n _ sp -> op n (evalV' <$> sp)
  EXReturn v  -> lift . creturn =<< evalV' v
  EXForce v   -> do
     -- enforced by the types; force takes a value of type U B, i.e. a thunk.
    VThunk v' <- evalV' v
    pure v'
  EXBind a b  -> do
     -- enforced by the types; bind takes a computation of type F A on the left, i.e. a return.
    CReturn a' <- evalC' a
    local (:> a') (evalC' b)

evalV' :: (Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Expr' V -> EnvC m (Value (Eval m))
evalV' = \case
  EXVar (Global n)  -> evalV =<< global n -- this will have to do until we store values in the global environment
  EXVar (Free v)    -> var v
  EXVar (Metavar m) -> case m of {}
  EXCon n _ fs      -> VCon n <$> traverse evalV' fs
  EXString s        -> pure $ VString s
  EXThunk b         -> VThunk <$> evalC' b -- this is definitely wrong, VThunk should definitely hold a computation


-- Combinators

type EnvC m = ReaderC (Snoc (Value (Eval m))) (Eval m)

global :: (Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Q Name -> EnvC m Expr
global n = do
  mod <- ask
  graph <- ask
  case lookupQ graph mod n of
    Just (_ :=: Just (DTerm v) ::: _) -> pure v
    _                                 -> fail $ "free variable: " <> show n

var :: HasCallStack => Index -> EnvC m (Value (Eval m))
var (Index v) = ReaderC $ \ env -> pure (env ! v)


lam :: forall m sig . Algebra sig m => [(Pattern Name, EnvC m (Comp (Eval m)))] -> EnvC m (Comp (Eval m))
lam cs = do
  env <- ask
  let clause p b = case p of
        PVal p -> Right (p, (`runReader` b) . foldl' (:>) env)
        PEff p -> Left  (p, (`runReader` b) . foldl' (:>) env)
  pure $ CLam (map (uncurry clause) cs)

($$) :: MonadFail m => EnvC m (Comp (Eval m)) -> EnvC m (Value (Eval m)) -> EnvC m (Comp (Eval m))
f $$ a = do
  CLam cs <- f
  let (es, vs) = partitionEithers cs
      handler h op sp k = fromMaybe (h op sp k) (foldMapA (\ (p, b) -> b . ($ k) <$> matchE p op sp) es)
      cont v = fromMaybe (fail "non-exhaustive patterns in lambda") (foldMapA (\ (p, b) -> b <$> matchV p v) vs)
  ReaderC $ \ env -> Eval $ \ h' k' -> runEval (handler h') (runEval h' k' . cont) (runReader env a)

infixl 9 $$

-- FIXME: I think this subverts scoped operations: we evaluate the arguments before the handler has had a chance to intervene. this doesn’t explain why it behaves the same when we use an explicit suspended computation, however.
op :: Q Name -> Snoc (EnvC m (Value (Eval m))) -> EnvC m (Comp (Eval m))
op n sp = do
  sp' <- sequenceA sp
  lift $ Eval $ \ h k -> runEval h k (h n sp' creturn)


-- Machinery

type Handler m = Q Name -> Snoc (Value m) -> (Value m -> m (Comp m)) -> m (Comp m)

runEval :: Handler (Eval m) -> (a -> m r) -> Eval m a -> m r
runEval hdl k (Eval m) = m hdl k

newtype Eval m a = Eval (forall r . Handler (Eval m) -> (a -> m r) -> m r)

instance Functor (Eval m) where
  fmap = liftM

instance Applicative (Eval m) where
  pure a = Eval $ \ _ k -> k a
  (<*>) = ap

instance Monad (Eval m) where
  m >>= f = Eval $ \ hdl k -> runEval hdl (runEval hdl k . f) m

instance MonadFail m => MonadFail (Eval m) where
  fail = lift . fail

instance MonadTrans Eval where
  lift m = Eval $ \ _ k -> m >>= k

instance Algebra sig m => Algebra sig (Eval m) where
  alg hdl sig ctx = Eval $ \ h k -> alg (runEval h pure . hdl) sig ctx >>= k


-- Values

data Value m
  -- | Neutral; variables, only used during quotation
  = VFree Level
  -- | Value; data constructors.
  | VCon (Q Name) (Snoc (Value m))
  -- | Value; strings.
  | VString Text
  -- | Thunks embed computations into values.
  | VThunk (Comp m)

vthunk :: Comp m -> Value m
vthunk = \case
  CReturn v -> v
  c         -> VThunk c

unit :: Value m
unit = VCon (["Data", "Unit"] :.: N "unit") Nil

-- | Terminal computations.
data Comp m
  -- | Neutral; effect operations, only used during quotation.
  = COp (Q Name) (Snoc (Value m)) (Value m)
  | CLam [Either (EffectPattern Name, EffectPattern (Value m) -> m (Comp m)) (ValuePattern Name, ValuePattern (Value m) -> m (Comp m))]
  | CReturn (Value m)

creturn :: Applicative m => Value m -> m (Comp m)
creturn = pure . \case
  VThunk c -> c
  v        -> CReturn v


-- Elimination

matchE :: MonadFail m => EffectPattern Name -> Q Name -> Snoc (Value m) -> Maybe ((Value m -> m (Comp m)) -> EffectPattern (Value m))
matchE p n' fs = case p of
  -- FIXME: I can’t see how this could possibly be correct
  PAll _     -> pure $ \ k -> PAll (VThunk (COp n' fs (cont k)))
  POp n ps _ -> mk <$ guard (n == n') <*> zipWithM matchV ps fs
  where
  mk sp k = POp n' sp (cont k)
  cont k = VThunk (CLam [Right (PVar __, unPVar k)])
  unPVar k = \case
    PVar v -> k v
    _      -> fail "unexpected non-variable pattern given to continuation"

matchV :: ValuePattern Name -> Value m -> Maybe (ValuePattern (Value m))
matchV = curry $ \case
  (PWildcard, _)          -> pure PWildcard
  (PVar _,    s)          -> pure (PVar s)
  (PCon n ps, VCon n' fs) -> PCon n' <$ guard (n == n') <*> zipWithM matchV ps fs
  (PCon{},    _)          -> empty


-- Quotation

quoteV :: Monad m => Level -> Value m -> m Expr
quoteV d = \case
  VFree lvl -> pure (XVar (Free (levelToIndex d lvl)))
  VCon n fs -> XCon n Nil <$> traverse (quoteV d) fs
  VString s -> pure $ XString s
  VThunk c  -> quoteC d c

quoteC :: Monad m => Level -> Comp m -> m Expr
quoteC d = \case
  COp q fs k -> XApp <$> quoteV d k <*> (XOp q Nil <$> traverse (quoteV d) fs)
  CLam cs    -> XLam <$> traverse (quoteClause d) cs
  CReturn v  -> quoteV d v

quoteClause :: Monad m => Level -> Either (EffectPattern Name, EffectPattern (Value m) -> m (Comp m)) (ValuePattern Name, ValuePattern (Value m) -> m (Comp m)) -> m (Pattern Name, Expr)
quoteClause d p = fmap (pn,) $ case p of
  Right (p, k) -> let (d', p') = fillV p in quoteC d' =<< k p'
  Left  (p, h) -> let (d', p') = fillV p in quoteC d' =<< h p'
  where
  pn = either (PEff . fst) (PVal . fst) p
  fillV :: Traversable t => t Name -> (Level, t (Value m))
  fillV = fill ((,) <$> succ <*> VFree) d
