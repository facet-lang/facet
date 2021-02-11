module Facet.Eval
( -- * Evaluation
  eval
  -- * Machinery
, Op(..)
, Handler(..)
, runEval
, Eval(..)
  -- * Values
, Value(..)
, quote
) where

import Control.Algebra hiding (Handler)
import Control.Applicative (Alternative(..))
import Control.Effect.Reader
import Control.Monad (foldM, guard, (<=<))
import Control.Monad.Trans.Class
import Data.Foldable (foldl')
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

eval :: (HasCallStack, Has (Reader Graph :+: Reader Module) sig m) => Expr -> Eval m (Value m (Var Void Level))
eval = force Nil <=< go Nil
  where
  go env = \case
    XVar (Global n)  -> pure $ VNe (Global n) Nil
    XVar (Free v)    -> pure $ env ! getIndex v
    XVar (Metavar m) -> case m of {}
    XTLam b          -> go env b
    XLam cs          -> pure $ VLam (map (\ (p, b) -> (p, \ p -> go (foldl' (:>) env p) b)) cs)
    XInst f _        -> go env f
    XApp  f a        -> do
      f' <- go env f
      app env f' (go env a)
    XCon n _ fs      -> VCon n <$> traverse (go env) fs
    XString s        -> pure $ VString s
    XOp n _ sp       -> do
      sp' <- traverse (go env) sp
      Eval $ \ h k -> runHandler h (Op n sp') k
  app env f a = case f of
    VNe h sp -> a >>= \ a' -> pure $ VNe h (sp:>a')
    -- FIXME: check to see if this handles any effects
    {-
    Σ ⊢op f ~> { [e;k] -> b, x -> y }     Σ, [e;k] -> b ⊢op a ~> a'
    ---------------------------------------------------------------
    Σ ⊢op f a ~> [x|->a']y
    -}
    VLam cs  -> a >>= force env >>= \ a' -> case' a' cs
    _        -> error "throw a real error (apply)"
  force env = \case
    VNe (Global n) sp -> do
      mod <- lift ask
      graph <- lift ask
      case lookupQ graph mod n of
        Just (_ :=: Just (DTerm v) ::: _) -> do
          v' <- go env v
          force env =<< foldM (app env) v' (pure <$> sp)
        _                                 -> error "throw a real error here"
    v                 -> pure v


-- Machinery

data Op a = Op (Q Name) (Stack a)

newtype Handler m r = Handler { runHandler :: Op (Value m (Var Void Level)) -> (Value m (Var Void Level) -> m r) -> m r }

runEval :: Handler m r -> (a -> m r) -> Eval m a -> m r
runEval hdl k (Eval m) = m hdl k

newtype Eval m a = Eval (forall r . Handler m r -> (a -> m r) -> m r)

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


-- Elimination

case' :: HasCallStack => Value m a -> [(Pattern Name, Pattern (Value m a) -> Eval m (Value m a))] -> Eval m (Value m a)
case' s = foldr (uncurry (match s)) (error "non-exhaustive patterns in lambda")
  where
  match s p f k = case p of
    PEff{}  -> k
    PVal p' -> maybe k (f . PVal) (value s p')
  value s = \case
    PWildcard -> pure PWildcard
    PVar _    -> pure (PVar s)
    PCon n ps
      | VCon n' fs <- s -> PCon n' <$ guard (n == n') <*> zipWithM value fs ps
    PCon{}    -> empty


-- Quotation

quote :: Level -> Value m (Var Void Level) -> Eval m Expr
quote d = \case
  VLam cs   -> XLam <$> traverse (\ (p, b) -> (p,) <$> let (d', p') = fill (\ d -> (succ d, VNe (Free d) Nil)) d p in quote d' =<< b p') cs
  VNe h sp  -> foldl' XApp (XVar (levelToIndex d <$> h)) <$> traverse (quote d) sp
  VCon n fs -> XCon n Nil <$> traverse (quote d) fs
  VString s -> pure $ XString s
