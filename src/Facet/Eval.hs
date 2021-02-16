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
import Control.Monad (ap, guard, liftM, (<=<))
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
eval = runReader Nil . go
  where
  go :: Expr -> ReaderC (Snoc (Value (Eval m))) (Eval m) (Comp (Eval m))
  go = \case
    XVar (Global n)  -> do
      mod <- lift ask
      graph <- lift ask
      case lookupQ graph mod n of
        Just (_ :=: Just (DTerm v) ::: _) -> go v
        _                                 -> error "throw a real error here"
    XVar (Free v)    -> asks (CReturn . (! getIndex v))
    XVar (Metavar m) -> case m of {}
    XTLam b          -> go b
    XInst f _        -> go f
    XLam cs          -> do
      env <- ask
      let (es, vs) = partitionEithers (map (\case{ (PEff e, b) -> Left (e, go b) ; (PVal v, b) -> Right (v, go b) }) cs)
          lamV = VThunk . CLam [pvar __] id
      pure $ CLam
        (map fst cs)
        (\ toph op k -> maybe (toph op k) (\ (f, b) -> runReader (f env :> lamV k) b) $ foldMapA (\ (p, b) -> (,b) <$> matchE p op) es)
        (\ v -> maybe (fail "non-exhaustive patterns in lambda") (\ (f, b) -> runReader (f env) b) $ foldMapA (\ (p, b) -> (,b) <$> matchV p v) vs)
    XApp  f a        -> do
      CLam _ h k <- force =<< go f
      extendHandler h (go a) >>= to >>= lift . k
    XCon n _ fs      -> CReturn . VCon n <$> traverse (to <=< go) fs
    XString s        -> pure $ CReturn $ VString s
    XOp n _ sp       -> do
      -- FIXME: I think this subverts scoped operations: we evaluate the arguments before the handler has had a chance to intervene. this doesn’t explain why it behaves the same when we use an explicit suspended computation, however.
      sp' <- traverse (to <=< go) sp
      lift $ Eval $ \ h k -> runEval h k (h (Op n sp') (pure . CReturn))
    where
    -- NB: CPS would probably be more faithful to Levy’s treatment
    to v = do
      CReturn v' <- pure v
      pure v'
    force = \case
      CReturn (VThunk b) -> pure b
      c                  -> pure c
    extendHandler ext m = ReaderC $ \ env -> do
      let Eval run = runReader env m
      Eval $ \ h -> run (ext h)


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

data Comp m
  -- | Neutral; effect operations, only used during quotation.
  = COp (Op (Value m)) (Value m)
  | CLam [Pattern Name] (Handler m -> Handler m) (Value m -> m (Comp m))
  | CReturn (Value m)


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
