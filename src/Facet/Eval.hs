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

eval :: forall r m sig . (HasCallStack, Has (Reader Graph :+: Reader Module) sig m) => Expr -> Eval r m (Value r m (Var Void Level))
eval = force Nil <=< go Nil
  where
  go env = \case
    XVar (Global n)  -> pure $ VNe (Global n) Nil
    XVar (Free v)    -> env ! getIndex v
    XVar (Metavar m) -> case m of {}
    XTLam b          -> go env b
    XLam cs          -> pure $ VLam (map fst cs) (Eval . body)
      where
      body :: Eval r m (Value r m (Var Void Level)) -> (Op r m (Value r m (Var Void Level)) -> m r) -> (Value r m (Var Void Level) -> m r) -> m r
      body v toph topk = runEval h k v
        where
        cs' = map (\ (p, e) -> (p, \ p' -> go (foldl' (:>) env p') e)) cs
        (es, vs) = partitionEithers (map (\case{ (PEff e, b) -> Left (e, b) ; (PVal v, b) -> Right (v, b) }) cs')
        -- run the effect handling cases
        h :: Op r m (Value r m (Var Void Level)) -> m r
        h op = foldr (\ (p, b) rest -> maybe rest (runEval h k . b . fmap pure . PEff) (matchE p op)) (toph op) es
        -- run the value handling cases
        k :: Value r m (Var Void Level) -> m r
        k v = runEval toph topk $ force env v >>= \ v' -> foldr (\ (p, b) rest -> maybe rest (b . fmap pure . PVal) (matchV p v')) (error "non-exhaustive patterns in lambda") vs
    XInst f _        -> go env f
    XApp  f a        -> do
      f' <- go env f
      app f' (go env a)
    XCon n _ fs      -> VCon n <$> traverse (go env) fs
    XString s        -> pure $ VString s
    XOp n _ sp       -> do
      sp' <- traverse (go env) sp
      Eval $ \ h _ -> h (Op n sp' pure)
  app f a = case f of
    VNe h sp -> pure $ VNe h (sp:>a)
    VLam _ b -> b a
    _        -> error "throw a real error (apply)"
  force env = \case
    VNe n sp -> forceN env n sp
    v        -> pure v
  forceN env (Global n)  sp = forceGlobal env n sp
  forceN _   (Free n)    sp = pure $ VNe (Free n) sp
  forceN _   (Metavar m) _  = case m of {}
  forceGlobal env n sp = do
    mod <- lift ask
    graph <- lift ask
    case lookupQ graph mod n of
      Just (_ :=: Just (DTerm v) ::: _) -> do
        v' <- go env v
        force env =<< foldM app v' sp
      _                                 -> error "throw a real error here"


-- Machinery

data Op r m a = Op (Q Name) (Stack (Value r m (Var Void Level))) (Value r m (Var Void Level) -> Eval r m a)

runEval :: (Op r m a -> m r) -> (a -> m r) -> Eval r m a -> m r
runEval hdl k (Eval m) = m hdl k

newtype Eval r m a = Eval ((Op r m a -> m r) -> (a -> m r) -> m r)

instance Functor (Eval r m) where
  fmap = liftM

instance Applicative (Eval r m) where
  pure a = Eval $ \ _ k -> k a
  (<*>) = ap

instance Monad (Eval r m) where
  m >>= f = Eval $ \ hdl k -> runEval (\ (Op q fs k') -> hdl (Op q fs (f <=< k'))) (runEval hdl k . f) m

instance MonadTrans (Eval r) where
  lift m = Eval $ \ _ k -> m >>= k


-- Values

data Value r m a
  = VLam [Pattern Name] (Eval r m (Value r m a) -> Eval r m (Value r m a))
  | VNe a (Stack (Eval r m (Value r m a)))
  | VOp (Q Name) (Stack (Value r m a)) (Value r m a)
  | VCon (Q Name) (Stack (Value r m a))
  | VString Text


-- Elimination

matchE :: EffectPattern Name -> Op r m (Value r m (Var Void Level)) -> Maybe (EffectPattern (Value r m (Var Void Level)))
matchE (POp n ps _) (Op n' fs k) = POp n' <$ guard (n == n') <*> zipWithM matchV ps fs <*> pure (VLam [PVal (PVar __)] (k =<<))

matchV :: ValuePattern Name -> Value r m a -> Maybe (ValuePattern (Value r m a))
matchV p s = case p of
  PWildcard -> pure PWildcard
  PVar _    -> pure (PVar s)
  PCon n ps
    | VCon n' fs <- s -> PCon n' <$ guard (n == n') <*> zipWithM matchV ps fs
  PCon{}    -> empty


-- Quotation

quote :: Level -> Value r m (Var Void Level) -> Eval r m Expr
quote d = \case
  VLam ps b  -> XLam <$> traverse (\ p -> (p,) <$> let (d', p') = fill (\ d -> (succ d, VNe (Free d) Nil)) d p in quote d' =<< b (pure (constructP p'))) ps
  VNe h sp   -> foldl' XApp (XVar (levelToIndex d <$> h)) <$> traverse (quote d =<<) sp
  VOp q fs k -> XApp <$> quote d k <*> (XOp q Nil <$> traverse (quote d) fs)
  VCon n fs  -> XCon n Nil <$> traverse (quote d) fs
  VString s  -> pure $ XString s


constructP :: Pattern (Value r m (Var Void Level)) -> Value r m (Var Void Level)
constructP = \case
  PVal v -> constructV v
  PEff e -> constructE e

constructV :: ValuePattern (Value r m (Var Void Level)) -> Value r m (Var Void Level)
constructV = \case
  PWildcard -> VString "wildcard" -- FIXME: maybe should provide a variable here anyway?
  PVar v    -> v
  PCon q fs -> VCon q (constructV <$> fs)

constructE :: EffectPattern (Value r m (Var Void Level)) -> Value r m (Var Void Level)
constructE (POp q fs k) = VOp q (constructV <$> fs) k
