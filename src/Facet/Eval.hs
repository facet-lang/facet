{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Eval
( -- * Evaluation
  eval
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
import Data.Function
import Data.Maybe (fromMaybe)
import Data.Semialign.Exts (Zip, zipWithM)
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
  thunk = vthunk <$> evalC e


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


lam :: (Algebra sig m, MonadFail m) => [(Pattern Name, EnvC m (Comp (Eval m)))] -> EnvC m (Comp (Eval m))
lam cs = do
  let (es, vs) = partitionEithers (map (\case{ (PEff e, b) -> Left (e, b) ; (PVal v, b) -> Right (v, b) }) cs)
      lamV = VThunk . CLam [pvar __] id
      withK b f k = local (\ env -> f (env :> lamV (runReader env . k))) b
  lam'
    (map fst cs)
    (\ op sp -> foldMapA (\ (p, b) -> withK b <$> matchE p op sp) es)
    (\ v -> foldMapA (\ (p, b) -> (`local` b) <$> matchV p v) vs)

lam'
  :: (Algebra sig m, MonadFail m)
  => [Pattern Name]
  -> (Q Name -> Snoc (Value (Eval m)) -> Maybe ((Value (Eval m) -> EnvC m (Comp (Eval m))) -> EnvC m (Comp (Eval m))))
  -> (Value (Eval m) -> Maybe (EnvC m (Comp (Eval m))))
  -> EnvC m (Comp (Eval m))
lam' ps h k = do
  env <- ask
  pure $ CLam ps
    (\ h' op sp k -> maybe (h' op sp k) (runReader env . ($ (lift . k))) (h op sp))
    (runReader env . fromMaybe (fail "non-exhaustive patterns in lambda") . k)

($$) :: MonadFail m => EnvC m (Comp (Eval m)) -> EnvC m (Value (Eval m)) -> EnvC m (Comp (Eval m))
f $$ a = do
  CLam _ h k <- f
  ReaderC $ \ env -> Eval $ \ h' k' -> runEval (h h') (runEval h' k' . k) (runReader env a)

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
unit = VCon (["Data", "Unit"] :.: U "unit") Nil

-- | Terminal computations.
data Comp m
  -- | Neutral; effect operations, only used during quotation.
  = COp (Q Name) (Snoc (Value m)) (Value m)
  | CLam [Pattern Name] (Handler m -> Handler m) (Value m -> m (Comp m))
  | CReturn (Value m)

creturn :: Applicative f => Value m -> f (Comp m)
creturn = pure . \case
  VThunk c -> c
  v        -> CReturn v


-- Elimination

matchE :: EffectPattern Name -> Q Name -> Snoc (Value m) -> Maybe (Snoc (Value m) -> Snoc (Value m))
matchE (POp n ps _) n' fs = guard (n == n') *> matchSpine ps fs

matchV :: ValuePattern Name -> Value m -> Maybe (Snoc (Value m) -> Snoc (Value m))
matchV = curry $ \case
  (PWildcard, _)          -> pure id
  (PVar _,    s)          -> pure (:> s)
  (PCon n ps, VCon n' fs) -> guard (n == n') *> matchSpine ps fs
  (PCon{},    _)          -> empty

matchSpine :: (Traversable t, Zip t) => t (ValuePattern Name) -> t (Value m) -> Maybe (Snoc (Value m) -> Snoc (Value m))
matchSpine ps sp = foldr (.) id <$> zipWithM matchV ps sp


-- Quotation

quoteV :: Monad m => Level -> Value m -> m Expr
quoteV d = \case
  VFree lvl -> pure (XVar (Free (levelToIndex d lvl)))
  VCon n fs -> XCon n Nil <$> traverse (quoteV d) fs
  VString s -> pure $ XString s
  VThunk c  -> quoteC d c

quoteC :: Monad m => Level -> Comp m -> m Expr
quoteC d = \case
  COp q fs k  -> XApp <$> quoteV d k <*> (XOp q Nil <$> traverse (quoteV d) fs)
  CLam ps h k -> XLam <$> traverse (quoteClause d h k) ps
  CReturn v   -> quoteV d v


quoteClause :: Monad m => Level -> (Handler m -> Handler m) -> (Value m -> m (Comp m)) -> Pattern Name -> m (Pattern Name, Expr)
quoteClause d h k p = fmap (p,) . quoteC d' =<< case p' of
  PVal p'           -> k (constructV p')
  PEff (POp q fs k) -> h (\ op sp _ -> pure (COp op sp k)) q (constructV <$> fs) (pure . CReturn)
  where
  (d', p') = fill ((,) <$> succ <*> VFree) d p


constructV :: ValuePattern (Value m) -> Value m
constructV = \case
  PWildcard -> unit -- FIXME: maybe should provide a variable here anyway?
  PVar v    -> v
  PCon q fs -> VCon q (constructV <$> fs)
