{-# LANGUAGE ScopedTypeVariables #-}
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
, quote
  -- * Elimination
, ecase
, case'
) where

import Control.Algebra hiding (Handler)
import Control.Applicative (Alternative(..))
import Control.Effect.Reader
import Control.Monad (ap, foldM, guard, liftM, (<=<))
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
    XVar (Free v)    -> env ! getIndex v
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
      Eval $ \ h _ -> h (Op n sp') pure
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

type Handler m r a = Op (Value m (Var Void Level)) -> (Value m (Var Void Level) -> Eval m a) -> m r

runEval :: Handler m r a -> (a -> m r) -> Eval m a -> m r
runEval hdl k (Eval m) = m hdl k

newtype Eval m a = Eval (forall r . Handler m r a -> (a -> m r) -> m r)

instance Functor (Eval m) where
  fmap = liftM

instance Applicative (Eval m) where
  pure a = Eval $ \ _ k -> k a
  (<*>) = ap

instance Monad (Eval m) where
  m >>= f = Eval $ \ hdl k -> runEval (\ op k' -> hdl op (f <=< k')) (runEval hdl k . f) m

instance MonadTrans Eval where
  lift m = Eval $ \ _ k -> m >>= k


-- Values

data Value m a
  -- FIXME: can we represent this as Val -> Eval Val without losing quotation?
  = VLam [(Pattern Name, Pattern (Eval m (Value m a)) -> Eval m (Value m a))]
  | VNe a (Stack (Value m a))
  | VCon (Q Name) (Stack (Value m a))
  | VString Text


-- Elimination

ecase :: forall m r . HasCallStack => [(EffectPattern Name, Pattern (Value m (Var Void Level)) -> Eval m (Value m (Var Void Level)))] -> Handler m r (Value m (Var Void Level)) -> Handler m r (Value m (Var Void Level))
ecase cs hdl = go
  where
  go :: Handler m r (Value m (Var Void Level))
  go = foldr combine hdl cs
  combine :: (EffectPattern Name, Pattern (Value m (Var Void Level)) -> Eval m (Value m (Var Void Level))) -> Handler m r (Value m (Var Void Level)) -> Handler m r (Value m (Var Void Level))
  combine (p, b) rest = \ op k -> case matchE p op (VLam [(PVal (PVar __), \case{ PVal (PVar v) -> k =<< v ; _ -> error "effect continuation called with non-PVar pattern" })]) of
    -- FIXME: runk is not obviously non-bogus
    Just p' -> let runk = runEval go runk . k in runEval go runk (b (PEff p'))
    Nothing -> rest op k

matchE :: EffectPattern Name -> Op (Value m a) -> Value m a -> Maybe (EffectPattern (Value m a))
matchE (POp n ps _) (Op n' fs) k = POp n' <$ guard (n == n') <*> zipWithM matchV ps fs <*> pure k


case' :: HasCallStack => Value m a -> [(Pattern Name, Pattern (Eval m (Value m a)) -> Eval m (Value m a))] -> Eval m (Value m a)
case' s = foldr (uncurry (matchP s)) (error "non-exhaustive patterns in lambda")
  where
  matchP s p f k = case p of
    PEff{}  -> k
    PVal p' -> maybe k (f . fmap pure . PVal) (matchV p' s)

matchV :: ValuePattern Name -> Value m a -> Maybe (ValuePattern (Value m a))
matchV p s = case p of
  PWildcard -> pure PWildcard
  PVar _    -> pure (PVar s)
  PCon n ps
    | VCon n' fs <- s -> PCon n' <$ guard (n == n') <*> zipWithM matchV ps fs
  PCon{}    -> empty


-- Quotation

quote :: Level -> Value m (Var Void Level) -> Eval m Expr
quote d = \case
  VLam cs   -> XLam <$> traverse (\ (p, b) -> (p,) <$> let (d', p') = fill (\ d -> (succ d, pure (VNe (Free d) Nil))) d p in quote d' =<< b p') cs
  VNe h sp  -> foldl' XApp (XVar (levelToIndex d <$> h)) <$> traverse (quote d) sp
  VCon n fs -> XCon n Nil <$> traverse (quote d) fs
  VString s -> pure $ XString s
