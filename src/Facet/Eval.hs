{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
  -- * Elimination
, vcase
) where

import Control.Algebra
import Control.Applicative (Alternative(..))
import Control.Effect.Reader
import Control.Monad (ap, foldM, guard, liftM, (<=<))
import Control.Monad.Trans.Class
import Data.Either (partitionEithers)
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

eval :: forall m sig . (HasCallStack, Has (Reader Graph :+: Reader Module) sig m) => Expr -> Eval m (Value m (Var Void Level))
eval = force Nil <=< go Nil
  where
  go env = \case
    XVar (Global n)  -> pure $ VNe (Global n) Nil
    XVar (Free v)    -> env ! getIndex v
    XVar (Metavar m) -> case m of {}
    XTLam b          -> go env b
    XLam cs          -> pure $ VLam (map fst cs) (\ v -> Eval (body v))
      where
      body :: forall r . Eval m (Value m (Var Void Level)) -> (Op m (Value m (Var Void Level)) -> m r) -> (Value m (Var Void Level) -> m r) -> m r
      body v toph topk = runEval h k v
        where
        cs' = map (\ (p, e) -> (p, \ p' -> go (foldl' (:>) env p') e)) cs
        (es, vs) = partitionEithers (map (\case{ (PEff e, b) -> Left (e, b) ; (PVal v, b) -> Right (v, b) }) cs')
        -- run the effect handling cases
        h :: Op m (Value m (Var Void Level)) -> m r
        h = foldr (\ (p, b) rest op -> case matchE p op of
          Just p' -> runEval h k (b (pure <$> PEff p'))
          Nothing -> rest op) toph es
        -- run the value handling cases
        k :: Value m (Var Void Level) -> m r
        k v = runEval toph topk $ vcase v vs
    XInst f _        -> go env f
    XApp  f a        -> do
      f' <- go env f
      app env f' (go env a)
    XCon n _ fs      -> VCon n <$> traverse (go env) fs
    XString s        -> pure $ VString s
    XOp n _ sp       -> do
      sp' <- traverse (go env) sp
      Eval $ \ h _ -> h (Op n sp' pure)
  app env f a = case f of
    VNe h sp -> a >>= \ a' -> pure $ VNe h (sp:>a')
    {-
    Σ ⊢op f ~> { [e;k] -> b, x -> y }     Σ, [e;k] -> b ⊢op a ~> a'
    ---------------------------------------------------------------
    Σ ⊢op f a ~> [x|->a']y
    -}
    VLam _ b -> b (a >>= force env)
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

data Op m a = Op (Q Name) (Stack (Value m (Var Void Level))) (Value m (Var Void Level) -> Eval m a)

runEval :: (Op m a -> m r) -> (a -> m r) -> Eval m a -> m r
runEval hdl k (Eval m) = m hdl k

newtype Eval m a = Eval (forall r . (Op m a -> m r) -> (a -> m r) -> m r)

instance Functor (Eval m) where
  fmap = liftM

instance Applicative (Eval m) where
  pure a = Eval $ \ _ k -> k a
  (<*>) = ap

instance Monad (Eval m) where
  m >>= f = Eval $ \ hdl k -> runEval (\ (Op q fs k') -> hdl (Op q fs (f <=< k'))) (runEval hdl k . f) m

instance MonadTrans Eval where
  lift m = Eval $ \ _ k -> m >>= k


-- Values

data Value m a
  = VLam [Pattern Name] (Eval m (Value m a) -> Eval m (Value m a))
  | VNe a (Stack (Value m a))
  | VOp (Q Name) (Stack (Value m a)) (Value m a)
  | VCon (Q Name) (Stack (Value m a))
  | VString Text


-- Elimination

matchE :: EffectPattern Name -> Op m (Value m (Var Void Level)) -> Maybe (EffectPattern (Value m (Var Void Level)))
matchE (POp n ps _) (Op n' fs k) = POp n' <$ guard (n == n') <*> zipWithM matchV ps fs <*> pure (VLam [PVal (PVar __)] (k =<<))


vcase :: HasCallStack => Value m a -> [(ValuePattern Name, Pattern (Eval m (Value m a)) -> Eval m (Value m a))] -> Eval m (Value m a)
vcase s = foldr (uncurry (matchP s)) (error "non-exhaustive patterns in lambda")
  where
  matchP s p f k = maybe k (f . fmap pure . PVal) (matchV p s)

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
  VLam ps b  -> XLam <$> traverse (\ p -> (p,) <$> let (d', p') = fill (\ d -> (succ d, VNe (Free d) Nil)) d p in quote d' =<< b (pure (constructP p'))) ps
  VNe h sp   -> foldl' XApp (XVar (levelToIndex d <$> h)) <$> traverse (quote d) sp
  VOp q fs k -> XApp <$> quote d k <*> (XOp q Nil <$> traverse (quote d) fs)
  VCon n fs  -> XCon n Nil <$> traverse (quote d) fs
  VString s  -> pure $ XString s


constructP :: Pattern (Value m (Var Void Level)) -> Value m (Var Void Level)
constructP = \case
  PVal v -> constructV v
  PEff e -> constructE e

constructV :: ValuePattern (Value m (Var Void Level)) -> Value m (Var Void Level)
constructV = \case
  PWildcard -> VString "wildcard" -- FIXME: maybe should provide a variable here anyway?
  PVar v    -> v
  PCon q fs -> VCon q (constructV <$> fs)

constructE :: EffectPattern (Value m (Var Void Level)) -> Value m (Var Void Level)
constructE (POp q fs k) = VOp q (constructV <$> fs) k
