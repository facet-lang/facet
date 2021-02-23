{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Eval
( -- * Evaluation
  eval
, eval'
  -- * Machinery
, Handler
, runEval
, Eval(..)
  -- * Values
, Value(..)
, unit
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

eval :: forall p m sig . (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Expr p -> Eval m (Value N (Eval m))
eval = runReader Nil . evalC

evalC :: (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Expr p -> EnvC m (Value N (Eval m))
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

evalV :: (Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Expr p -> EnvC m (Value P (Eval m))
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

eval' :: (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Expr' u -> EnvC m (Value u (Eval m))
eval' = \case
  EXTLam b          -> eval' b
  EXInst f _        -> eval' f
  EXLam cs          -> lam (fmap eval' <$> cs)
  EXApp  f a        -> eval' f $$ eval' a
  EXOp n _ sp       -> op n (eval' <$> sp)
  EXReturn v        -> lift . creturn =<< eval' v
  EXForce v         -> do
     -- enforced by the types; force takes a value of type U B, i.e. a thunk.
    VThunk v' <- eval' v
    pure v'
  EXBind a b        -> do
     -- enforced by the types; bind takes a computation of type F A on the left, i.e. a return.
    VReturn a' <- eval' a
    local (:> a') (eval' b)
  EXVar (Global n)  -> evalV =<< global n -- this will have to do until we store values in the global environment
  EXVar (Free v)    -> var v
  EXVar (Metavar m) -> case m of {}
  EXCon n _ fs      -> VCon n <$> traverse eval' fs
  EXString s        -> pure $ VString s
  EXThunk b         -> VThunk <$> eval' b -- this is definitely wrong, VThunk should definitely hold a computation


-- Combinators

type EnvC m = ReaderC (Snoc (Value P (Eval m))) (Eval m)

global :: (Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Q Name -> EnvC m (Expr P)
global n = do
  mod <- ask
  graph <- ask
  case lookupQ graph mod n of
    Just (_ :=: Just (DTerm v) ::: _) -> pure v
    _                                 -> fail $ "free variable: " <> show n

var :: HasCallStack => Index -> EnvC m (Value P (Eval m))
var (Index v) = ReaderC $ \ env -> pure (env ! v)


lam :: forall m sig . Algebra sig m => [(Pattern Name, EnvC m (Value N (Eval m)))] -> EnvC m (Value N (Eval m))
lam cs = do
  env <- ask
  let clause p b = case p of
        PVal p -> Right (p, (`runReader` b) . foldl' (:>) env)
        PEff p -> Left  (p, (`runReader` b) . foldl' (:>) env)
  pure $ VLam (map (uncurry clause) cs)

($$) :: MonadFail m => EnvC m (Value N (Eval m)) -> EnvC m (Value P (Eval m)) -> EnvC m (Value N (Eval m))
f $$ a = do
  VLam cs <- f
  let (es, vs) = partitionEithers cs
      handler h op sp k = fromMaybe (h op sp k) (foldMapA (\ (p, b) -> b . ($ k) <$> matchE p op sp) es)
      cont v = fromMaybe (fail "non-exhaustive patterns in lambda") (foldMapA (\ (p, b) -> b <$> matchV p v) vs)
  ReaderC $ \ env -> Eval $ \ h' k' -> runEval (handler h') (runEval h' k' . cont) (runReader env a)

infixl 9 $$

-- FIXME: I think this subverts scoped operations: we evaluate the arguments before the handler has had a chance to intervene. this doesn’t explain why it behaves the same when we use an explicit suspended computation, however.
op :: Q Name -> Snoc (EnvC m (Value P (Eval m))) -> EnvC m (Value N (Eval m))
op n sp = do
  sp' <- sequenceA sp
  lift $ Eval $ \ h k -> runEval h k (h n sp' creturn)


-- Machinery

type Handler m = Q Name -> Snoc (Value P m) -> (Value P m -> m (Value N m)) -> m (Value N m)

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

data Value u m where
  -- | Neutral; variables, only used during quotation
  VFree :: Level -> Value P m
  -- | Value; data constructors.
  VCon :: Q Name -> Snoc (Value P m) -> Value P m
  -- | Value; strings.
  VString :: Text -> Value P m
  -- | Thunks embed computations into values.
  VThunk :: Value N m -> Value P m
  -- | Neutral; effect operations, only used during quotation.
  VOp :: Q Name -> Snoc (Value P m) -> Value P m -> Value N m
  VLam :: [Either (EffectPattern Name, EffectPattern (Value P m) -> m (Value N m)) (ValuePattern Name, ValuePattern (Value P m) -> m (Value N m))] -> Value N m
  VReturn :: Value P m -> Value N m

vthunk :: Value N m -> Value P m
vthunk = \case
  VReturn v -> v
  c         -> VThunk c

unit :: Value P m
unit = VCon (["Data", "Unit"] :.: N "unit") Nil

creturn :: Applicative m => Value P m -> m (Value N m)
creturn = pure . \case
  VThunk c -> c
  v        -> VReturn v


-- Elimination

matchE :: MonadFail m => EffectPattern Name -> Q Name -> Snoc (Value P m) -> Maybe ((Value P m -> m (Value N m)) -> EffectPattern (Value P m))
matchE p n' fs = case p of
  -- FIXME: I can’t see how this could possibly be correct
  PAll _     -> pure $ \ k -> PAll (VThunk (VOp n' fs (cont k)))
  POp n ps _ -> mk <$ guard (n == n') <*> zipWithM matchV ps fs
  where
  mk sp k = POp n' sp (cont k)
  cont k = VThunk (VLam [Right (PVar __, unPVar k)])
  unPVar k = \case
    PVar v -> k v
    _      -> fail "unexpected non-variable pattern given to continuation"

matchV :: ValuePattern Name -> Value P m -> Maybe (ValuePattern (Value P m))
matchV = curry $ \case
  (PWildcard, _)          -> pure PWildcard
  (PVar _,    s)          -> pure (PVar s)
  (PCon n ps, VCon n' fs) -> PCon n' <$ guard (n == n') <*> zipWithM matchV ps fs
  (PCon{},    _)          -> empty


-- Quotation

quoteV :: Monad m => Level -> Value P m -> m (Expr P)
quoteV d = \case
  VFree lvl -> pure (XVar (Free (levelToIndex d lvl)))
  VCon n fs -> XCon n Nil <$> traverse (quoteV d) fs
  VString s -> pure $ XString s
  VThunk c  -> quoteC d c

quoteC :: Monad m => Level -> Value N m -> m (Expr P)
quoteC d = \case
  VOp q fs k -> XApp <$> quoteV d k <*> (XOp q Nil <$> traverse (quoteV d) fs)
  VLam cs    -> XLam <$> traverse (quoteClause d) cs
  VReturn v  -> quoteV d v

quoteClause :: Monad m => Level -> Either (EffectPattern Name, EffectPattern (Value P m) -> m (Value N m)) (ValuePattern Name, ValuePattern (Value P m) -> m (Value N m)) -> m (Pattern Name, Expr P)
quoteClause d p = fmap (pn,) $ case p of
  Right (p, k) -> let (d', p') = fillV p in quoteC d' =<< k p'
  Left  (p, h) -> let (d', p') = fillV p in quoteC d' =<< h p'
  where
  pn = either (PEff . fst) (PVal . fst) p
  fillV :: Traversable t => t Name -> (Level, t (Value P m))
  fillV = fill ((,) <$> succ <*> VFree) d
