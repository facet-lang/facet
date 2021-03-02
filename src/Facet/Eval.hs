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
, quote
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

eval :: forall m sig . (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Expr -> Eval m (Value (Eval m))
eval = runReader Nil . eval'

eval' :: (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Expr -> EnvC m (Value (Eval m))
eval' = \case
  XTLam b          -> eval' b
  XInst f _        -> eval' f
  XLam cs          -> lam (fmap eval' <$> cs)
  XApp  f a        -> eval' f $$ eval' a
  XOp n _ sp       -> op n (eval' <$> sp)
  XReturn v        -> lift . creturn =<< eval' v
  XForce v         -> do
     -- enforced by the types; force takes a value of type U B, i.e. a thunk.
    VThunk v' <- eval' v
    pure v'
  XBind a b        -> do
     -- enforced by the types; bind takes a computation of type F A on the left, i.e. a return.
    VReturn a' <- eval' a
    local (:> a') (eval' b)
  XVar (Global n)  -> eval' =<< global n -- this will have to do until we store values in the global environment
  XVar (Free v)    -> var v
  XVar (Metavar m) -> case m of {}
  XCon n _ fs      -> VCon n <$> traverse eval' fs
  XString s        -> pure $ VString s
  XThunk b         -> VThunk <$> eval' b -- this is definitely wrong, VThunk should definitely hold a computation


-- Combinators

type EnvC m = ReaderC (Snoc (Value (Eval m))) (Eval m)

global :: (Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => QName -> EnvC m Expr
global n = do
  mod <- ask
  graph <- ask
  case lookupQ graph mod n of
    Just (_ :=: DTerm (Just v) _) -> pure (getPos v)
    _                             -> fail $ "free variable: " <> show n

var :: HasCallStack => Index -> EnvC m (Value (Eval m))
var (Index v) = ReaderC $ \ env -> pure (env ! v)


lam :: forall m sig . Algebra sig m => [(Pattern Name, EnvC m (Value (Eval m)))] -> EnvC m (Value (Eval m))
lam cs = do
  env <- ask
  let clause p b = case p of
        PVal p -> Right (p, (`runReader` b) . foldl' (:>) env)
        PEff p -> Left  (p, (`runReader` b) . foldl' (:>) env)
  pure $ VLam (map (uncurry clause) cs)

($$) :: MonadFail m => EnvC m (Value (Eval m)) -> EnvC m (Value (Eval m)) -> EnvC m (Value (Eval m))
f $$ a = do
  VLam cs <- f
  let (es, vs) = partitionEithers cs
      handler h op sp k = fromMaybe (h op sp k) (foldMapA (\ (p, b) -> b . ($ k) <$> matchE p op sp) es)
      cont v = fromMaybe (fail "non-exhaustive patterns in lambda") (foldMapA (\ (p, b) -> b <$> matchV p v) vs)
  ReaderC $ \ env -> Eval $ \ h' k' -> runEval (handler h') (runEval h' k' . cont) (runReader env a)

infixl 9 $$

-- FIXME: I think this subverts scoped operations: we evaluate the arguments before the handler has had a chance to intervene. this doesn’t explain why it behaves the same when we use an explicit suspended computation, however.
op :: QName -> Snoc (EnvC m (Value (Eval m))) -> EnvC m (Value (Eval m))
op n sp = do
  sp' <- sequenceA sp
  lift $ Eval $ \ h k -> runEval h k (h n sp' creturn)


-- Machinery

type Handler m = QName -> Snoc (Value m) -> (Value m -> m (Value m)) -> m (Value m)

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
  | VCon QName (Snoc (Value m))
  -- | Value; strings.
  | VString Text
  -- | Thunks embed computations into values.
  | VThunk (Value m)
  -- | Neutral; effect operations, only used during quotation.
  | VOp QName (Snoc (Value m)) (Value m)
  | VLam [Either (EffectPattern Name, EffectPattern (Value m) -> m (Value m)) (ValuePattern Name, ValuePattern (Value m) -> m (Value m))]
  | VReturn (Value m)

unit :: Value m
unit = VCon (["Data", "Unit"] :.: N "unit") Nil

creturn :: Applicative m => Value m -> m (Value m)
creturn = pure . \case
  VThunk c -> c
  v        -> VReturn v


-- Elimination

matchE :: MonadFail m => EffectPattern Name -> QName -> Snoc (Value m) -> Maybe ((Value m -> m (Value m)) -> EffectPattern (Value m))
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

matchV :: ValuePattern Name -> Value m -> Maybe (ValuePattern (Value m))
matchV = curry $ \case
  (PWildcard, _)          -> pure PWildcard
  (PVar _,    s)          -> pure (PVar s)
  (PCon n ps, VCon n' fs) -> PCon n' <$ guard (n == n') <*> zipWithM matchV ps fs
  (PCon{},    _)          -> empty


-- Quotation

quote :: Monad m => Level -> Value m -> m Expr
quote d = \case
  VFree lvl  -> pure (XVar (Free (levelToIndex d lvl)))
  VCon n fs  -> XCon n Nil <$> traverse (quote d) fs
  VString s  -> pure $ XString s
  VThunk c   -> XThunk <$> quote d c

  VOp q fs k -> XApp . XForce <$> quote d k <*> (XThunk . XOp q Nil <$> traverse (quote d) fs)
  VLam cs    -> XLam <$> traverse (quoteClause d) cs
  VReturn v  -> XReturn <$> quote d v

quoteClause :: Monad m => Level -> Either (EffectPattern Name, EffectPattern (Value m) -> m (Value m)) (ValuePattern Name, ValuePattern (Value m) -> m (Value m)) -> m (Pattern Name, Expr)
quoteClause d p = fmap (pn,) $ case p of
  Right (p, k) -> let (d', p') = fillV p in quote d' =<< k p'
  Left  (p, h) -> let (d', p') = fillV p in quote d' =<< h p'
  where
  pn = either (PEff . fst) (PVal . fst) p
  fillV :: Traversable t => t Name -> (Level, t (Value m))
  fillV = fill ((,) <$> succ <*> VFree) d
