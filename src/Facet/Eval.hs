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
import Data.Function
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
  XTLam b          -> evalC b
  XInst f _        -> evalC f
  XLam cs          -> do
    env <- ask
    let (es, vs) = partitionEithers (map (\case{ (PEff e, b) -> Left (e, evalC b) ; (PVal v, b) -> Right (v, evalC b) }) cs)
        lamV = VThunk . CLam [pvar __] id
    pure $ CLam
      (map fst cs)
      (\ toph op k -> maybe (toph op k) (\ (f, b) -> runReader (f env :> lamV k) b) $ foldMapA (\ (p, b) -> (,b) <$> matchE p op) es)
      (\ v -> maybe (fail "non-exhaustive patterns in lambda") (\ (f, b) -> runReader (f env) b) $ foldMapA (\ (p, b) -> (,b) <$> matchV p v) vs)
  XApp  f a        -> do
    let force v = do
          VThunk c <- pure v
          pure c
    (force =<< evalV f) $$ evalV a
  XOp n _ sp       -> do
    -- FIXME: I think this subverts scoped operations: we evaluate the arguments before the handler has had a chance to intervene. this doesn’t explain why it behaves the same when we use an explicit suspended computation, however.
    sp' <- traverse evalV sp
    lift $ Eval $ \ h k -> runEval h k (h (Op n sp') creturn)
  XVar{}           -> return
  XCon{}           -> return
  XString{}        -> return
  where
  return = creturn =<< evalV e
  -- NB: CPS would probably be more faithful to Levy’s treatment

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
  thunk = VThunk <$> evalC e


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


($$) :: MonadFail m => EnvC m (Comp (Eval m)) -> EnvC m (Value (Eval m)) -> EnvC m (Comp (Eval m))
f $$ a = do
  CLam _ h k <- f
  ReaderC $ \ env -> Eval $ \ h' k' -> runEval (h h') (runEval h' k' . k) (runReader env a)

infixl 9 $$


-- Machinery

data Op a = Op (Q Name) (Snoc a)

type Handler m = Op (Value m) -> (Value m -> m (Comp m)) -> m (Comp m)

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

unit :: Value m
unit = VCon (["Data", "Unit"] :.: U "unit") Nil

-- | Terminal computations.
data Comp m
  -- | Neutral; effect operations, only used during quotation.
  = COp (Op (Value m)) (Value m)
  | CLam [Pattern Name] (Handler m -> Handler m) (Value m -> m (Comp m))
  | CReturn (Value m)

creturn :: Applicative f => Value m -> f (Comp m)
creturn = pure . \case
  VThunk c -> c
  v        -> CReturn v


-- Elimination

matchE :: EffectPattern Name -> Op (Value m) -> Maybe (Snoc (Value m) -> Snoc (Value m))
matchE (POp n ps _) (Op n' fs) = foldr (.) id <$ guard (n == n') <*> zipWithM matchV ps fs

matchV :: ValuePattern Name -> Value m -> Maybe (Snoc (Value m) -> Snoc (Value m))
matchV p s = case p of
  PWildcard -> pure id
  PVar _    -> pure (:> s)
  PCon n ps
    | VCon n' fs <- s -> foldr (.) id <$ guard (n == n') <*> zipWithM matchV ps fs
  PCon{}    -> empty


-- Quotation

quoteV :: Monad m => Level -> Value m -> m Expr
quoteV d = \case
  VFree lvl -> pure (XVar (Free (levelToIndex d lvl)))
  VCon n fs -> XCon n Nil <$> traverse (quoteV d) fs
  VString s -> pure $ XString s
  VThunk c  -> quoteC d c

quoteC :: Monad m => Level -> Comp m -> m Expr
quoteC d = \case
  COp (Op q fs) k -> XApp <$> quoteV d k <*> (XOp q Nil <$> traverse (quoteV d) fs)
  CLam ps h k     -> XLam <$> traverse (quoteClause d h k) ps
  CReturn v       -> quoteV d v


quoteClause :: Monad m => Level -> (Handler m -> Handler m) -> (Value m -> m (Comp m)) -> Pattern Name -> m (Pattern Name, Expr)
quoteClause d h k p = fmap (p,) . quoteC d' =<< case p' of
  PVal p'           -> k (constructV p')
  PEff (POp q fs k) -> h (\ op _ -> pure (COp op k)) (Op q (constructV <$> fs)) (pure . CReturn)
  where
  (d', p') = fill ((,) <$> succ <*> VFree) d p


constructV :: ValuePattern (Value m) -> Value m
constructV = \case
  PWildcard -> unit -- FIXME: maybe should provide a variable here anyway?
  PVar v    -> v
  PCon q fs -> VCon q (constructV <$> fs)
