module Facet.Eval
( -- * Evaluation
  eval
  -- * Machinery
, Op(..)
, runEval
, Eval(..)
  -- * Values
, Value(..)
, quote
) where

import Control.Algebra
import Control.Applicative (Alternative(..))
import Control.Effect.Reader
import Control.Monad (guard)
import Control.Monad.Trans.Class
import Data.Foldable (foldl')
import Data.Semialign.Exts (zipWithM)
import Data.Text (Text)
import Facet.Core.Module
import Facet.Core.Term
import Facet.Graph
import Facet.Name hiding (Op)
import Facet.Stack
import Facet.Syntax
import GHC.Stack (HasCallStack)
import Prelude hiding (zipWith)

eval :: (HasCallStack, Has (Reader Graph :+: Reader Module) sig m) => Expr -> Eval m (Value m Level)
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
        -- FIXME: check to see if this handles any effects
        VLam cs -> case' a' cs
        _       -> error "throw a real error (apply)"
    XCon n _ fs      -> VCon n <$> traverse (go env) fs
    XString s        -> pure $ VString s
    XOp n _ sp       -> do
      sp' <- traverse (go env) sp
      Eval $ \ h k -> h (Op n sp') k


-- Machinery

data Op a = Op (Q Name) (Stack a)

runEval :: (forall x . Op (Value m x) -> (Value m x -> m r) -> m r) -> (a -> m r) -> Eval m a -> m r
runEval hdl k (Eval m) = m hdl k

newtype Eval m a = Eval (forall r . (forall x . Op (Value m x) -> (Value m x -> m r) -> m r) -> (a -> m r) -> m r)

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
  | VVar a
  | VCon (Q Name) (Stack (Value m a))
  | VString Text


-- Elimination

case' :: HasCallStack => Value m a -> [(Pattern Name, Pattern (Value m a) -> Eval m (Value m a))] -> Eval m (Value m a)
case' s = foldr (uncurry (match s)) (error "non-exhaustive patterns in lambda")
  where
  match s p f k = case p of
    PAll _  -> f (PAll s)
    PEff{}  -> k
    PVal p' -> maybe k (f . PVal) (value s p')
  value s p = case p of
    PWildcard -> pure PWildcard
    PVar _    -> pure (PVar s)
    PCon n ps
      | VCon n' fs <- s -> PCon n' <$ guard (n == n') <*> zipWithM value fs ps
    PCon{}    -> empty


-- Quotation

quote :: Level -> Value m Level -> Eval m Expr
quote d = \case
  VLam cs   -> XLam <$> traverse (\ (p, b) -> (p,) <$> let (d', p') = fill (\ d -> (succ d, VVar d)) d p in quote d' =<< b p') cs
  VVar h    -> pure $ XVar (Free (levelToIndex d h))
  VCon n fs -> XCon n Nil <$> traverse (quote d) fs
  VString s -> pure $ XString s
