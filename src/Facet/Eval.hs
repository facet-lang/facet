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

import           Control.Algebra
import           Control.Effect.Reader
import           Control.Monad (guard)
import           Control.Monad.Trans.Class
import           Data.Either (fromRight)
import           Data.Foldable (asum, foldl')
import           Data.Semialign.Exts (zipWithM)
import           Data.Text (Text)
import           Data.Void (Void)
import           Facet.Core.Module
import           Facet.Core.Term
import qualified Facet.Core.Type as T
import           Facet.Graph
import           Facet.Name
import           Facet.Stack
import           Facet.Syntax
import           GHC.Stack (HasCallStack)

eval :: Has (Reader Graph :+: Reader Module) sig m => Expr -> Eval m (Value m a)
eval = go Nil
  where
  go env = \case
    XVar (Global n)  -> do
      mod <- lift ask
      graph <- lift ask
      case lookupQ graph mod n of
        Just (_ :=: Just (DTerm v) ::: _) -> go env v
        _                                 -> error "throw a real error here"
    XVar (Free v)    -> pure $ fromRight (error ("type variable at index " <> show v)) (env ! getIndex v)
    XVar (Metavar m) -> case m of {}
    XTLam b          -> pure $ VTLam (\ _T -> go (env :> Left _T) b)
    XLam cs          -> pure $ VLam (map (\ (p, b) -> (p, \ p -> go (foldl' (\ env' v -> env' :> Right v) env p) b)) cs)
    XInst f a        -> ($$$ T.eval mempty env a) =<< go env f
    XApp  f a        -> do
      f' <- go env f
      a' <- go env a
      f' $$ a'
    XCon n ts fs     -> VCon n (T.eval mempty env <$> ts) <$> traverse (go env) fs
    XString s        -> pure $ VString s
    XOp n            -> pure $ VOp n Nil Nil


-- Machinery

runEval :: (Q Name -> Stack T.Type -> Stack (Value m ()) -> (Value m () -> m r) -> m r) -> (a -> m r) -> Eval m a -> m r
runEval hdl k (Eval m) = m hdl k

newtype Eval m a = Eval (forall r . (Q Name -> Stack T.Type -> Stack (Value m ()) -> (Value m () -> m r) -> m r) -> (a -> m r) -> m r)

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
  = VTLam (T.Type -> Eval m (Value m a))
  | VLam [(Pattern Name, Pattern (Value m a) -> Eval m (Value m a))]
  | VNe a (Stack T.Type) (Stack (Value m a))
  | VCon (Q Name) (Stack T.Type) (Stack (Value m a))
  | VString Text
  | VOp (Q Name) (Stack T.Type) (Stack (Value m a))

var :: a -> Value m a
var v = VNe v Nil Nil


-- Elimination

($$) :: HasCallStack => Value m a -> Value m a -> Eval m (Value m a)
VNe h ts es $$ a = pure $ VNe h ts (es :> a)
VLam cs     $$ a = case' a cs
VOp h ts es $$ a = pure $ VOp h ts (es :> a)
_           $$ _ = error "can’t apply"

infixl 9 $$


($$$) :: HasCallStack => Value m a -> T.Type -> Eval m (Value m a)
VNe h ts es $$$ t = pure $ VNe h (ts :> t) es
VTLam b     $$$ t = b t
VOp h ts es $$$ t = pure $ VOp h (ts :> t) es
_           $$$ _ = error "can’t instantiate"

infixl 9 $$$


case' :: HasCallStack => Value m a -> [(Pattern Name, Pattern (Value m a) -> Eval m (Value m a))] -> Eval m (Value m a)
case' s cs = case asum (map (\ (p, f) -> f <$> match s p) cs) of
  Just v -> v
  _      -> error "non-exhaustive patterns in lambda"

match :: Value m a -> Pattern b -> Maybe (Pattern (Value m a))
match = curry $ \case
  (s, PAll _)  -> Just (PAll s)
  -- FIXME: match effect patterns against computations (?)
  (_, PEff{})  -> Nothing
  (s, PVal p') -> PVal <$> value s p'
  where
  value = curry $ \case
    (_,            PWildcard) -> Just PWildcard
    (s,            PVar _)    -> Just (PVar s)
    -- NB: we’re assuming they’re the same length because they’ve passed elaboration.
    (VCon n' _ fs, PCon n ps) -> PCon n' <$ guard (n == n') <*> zipWithM value fs ps
    (_,            PCon{})    -> Nothing


-- Quotation

quoteExpr :: Level -> Value m (Var Void Level) -> Eval m Expr
quoteExpr d = \case
  VTLam b      -> XTLam <$> (quoteExpr (succ d) =<< b (T.free d))
  VLam cs      -> XLam <$> traverse (\ (p, b) -> (p,) <$> let (d', p') = fill (\ d -> (succ d, var (Free d))) d p in quoteExpr d' =<< b p') cs
  VNe h ts as  -> foldl' XApp (foldl' XInst (XVar (levelToIndex d <$> h)) (T.quote d <$> ts)) <$> traverse (quoteExpr d) as
  VCon n ts fs -> XCon n (T.quote d <$> ts) <$> traverse (quoteExpr d) fs
  VString s    -> pure $ XString s
  VOp n ts sp  -> foldl' XApp (foldl' XInst (XOp n) (T.quote d <$> ts)) <$> traverse (quoteExpr d) sp
