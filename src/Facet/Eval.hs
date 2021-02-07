module Facet.Eval
( -- * Evaluation
  eval
  -- * Machinery
, runEval
, Eval(..)
  -- * Values
, Value(..)
, quoteExpr
) where

import Control.Algebra
import Control.Applicative (Alternative(..))
import Control.Effect.Reader
import Control.Monad (guard)
import Control.Monad.Trans.Class
import Data.Foldable (asum, foldl')
import Data.Maybe (fromMaybe)
import Data.Semialign.Exts (zipWithM)
import Data.Text (Text)
import Data.Void (Void)
import Facet.Core.Module
import Facet.Core.Term
import Facet.Graph
import Facet.Name
import Facet.Stack
import Facet.Syntax
import GHC.Stack (HasCallStack)

eval :: (HasCallStack, Has (Reader Graph :+: Reader Module) sig m) => Expr -> Eval m (Value m (Var Void Level))
eval = go Nil
  where
  go env = \case
    XVar (Global n)  -> do
      mod <- lift ask
      graph <- lift ask
      case lookupQ graph mod n of
        Just (_ :=: Just (DTerm v) ::: _) -> go env v
        _                                 -> error "throw a real error here"
    XVar (Free v)    -> pure $ env ! getIndex v
    XVar (Metavar m) -> case m of {}
    XTLam b          -> go env b
    XLam cs          -> pure $ VLam (map (\ (p, b) -> (p, \ p -> go (foldl' (:>) env p) b)) cs)
    XInst f _        -> go env f
    XApp  f a        -> do
      f' <- go env f
      a' <- go env a
      case f' of
        VLam cs -> case' a' cs
        _       -> error "throw a real error (apply)"
    XCon n _ fs      -> VCon n <$> traverse (go env) fs
    XString s        -> pure $ VString s
    XOp n _ sp       -> do
      sp' <- traverse (go env) sp
      Eval $ \ h k -> h n sp' k


-- Machinery

runEval :: (Q Name -> Stack (Value m (Var Void Level)) -> (Value m (Var Void Level) -> m r) -> m r) -> (a -> m r) -> Eval m a -> m r
runEval hdl k (Eval m) = m hdl k

newtype Eval m a = Eval (forall r . (Q Name -> Stack (Value m (Var Void Level)) -> (Value m (Var Void Level) -> m r) -> m r) -> (a -> m r) -> m r)

instance Functor (Eval m) where
  fmap f (Eval m) = Eval $ \ hdl k -> m hdl (k . f)

instance Applicative (Eval m) where
  pure a = Eval $ \ _ k -> k a
  f <*> a = Eval $ \ hdl k -> runEval hdl (\ f' -> runEval hdl (\ a' -> k $! f' a') a) f

instance Monad (Eval m) where
  m >>= f = Eval $ \ hdl k -> runEval hdl (runEval hdl k . f) m

instance MonadTrans Eval where
  lift m = Eval $ \ _ k -> m >>= k


-- Values

data Value m a
  = VLam [(Pattern Name, Pattern (Value m a) -> Eval m (Value m a))]
  | VNe a (Stack (Value m a))
  | VCon (Q Name) (Stack (Value m a))
  | VString Text
  | VOp (Q Name) (Stack (Value m a))

var :: a -> Value m a
var v = VNe v Nil


-- Elimination

case' :: HasCallStack => Value m a -> [(Pattern Name, Pattern (Value m a) -> Eval m (Value m a))] -> Eval m (Value m a)
case' s cs = fromMaybe (error "non-exhaustive patterns in lambda") (asum (map (\ (p, f) -> f <$> match s p) cs))

match :: Alternative f => Value m a -> Pattern b -> f (Pattern (Value m a))
match = curry $ \case
  (s, PAll _)  -> pure (PAll s)
  -- FIXME: match effect patterns against computations (?)
  (_, PEff{})  -> empty
  (s, PVal p') -> PVal <$> value s p'
  where
  value = curry $ \case
    (_,          PWildcard) -> pure PWildcard
    (s,          PVar _)    -> pure (PVar s)
    -- NB: we’re assuming they’re the same length because they’ve passed elaboration.
    (VCon n' fs, PCon n ps) -> PCon n' <$ guard (n == n') <*> zipWithM value fs ps
    (_,          PCon{})    -> empty


-- Quotation

quoteExpr :: Level -> Value m (Var Void Level) -> Eval m Expr
quoteExpr d = \case
  VLam cs   -> XLam <$> traverse (\ (p, b) -> (p,) <$> let (d', p') = fill (\ d -> (succ d, var (Free d))) d p in quoteExpr d' =<< b p') cs
  VNe h as  -> foldl' XApp (XVar (levelToIndex d <$> h)) <$> traverse (quoteExpr d) as
  VCon n fs -> XCon n Nil <$> traverse (quoteExpr d) fs
  VString s -> pure $ XString s
  VOp n sp  -> XOp n Nil <$> traverse (quoteExpr d) sp
