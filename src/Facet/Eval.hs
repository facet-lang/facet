{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
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
, unit
  -- * Quotation
, quoteV
) where

import Control.Algebra hiding (Handler)
import Control.Applicative (Alternative(..))
import Control.Effect.Reader
import Control.Monad (ap, foldM, guard, liftM, (<=<))
import Control.Monad.Trans.Class
import Data.Either (partitionEithers)
import Data.Foldable (foldl')
import Data.Function
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

eval :: forall m sig . (HasCallStack, Has (Reader Graph :+: Reader Module) sig m) => Expr -> Eval m (Value (Eval m))
eval = force Nil <=< go Nil
  where
  go env = \case
    XVar (Global n)  -> pure $ VNe (Global n) Nil
    XVar (Free v)    -> env ! getIndex v
    XVar (Metavar m) -> case m of {}
    XTLam b          -> go env b
    XInst f _        -> go env f
    XLam cs          -> pure $ VLam (map fst cs) body
      where
      -- FIXME: it’s really uncomfortable that this takes computations to computations. function application fundamentally is, and should remain, value to computation. effect handling is different and should be applied disjointly.
      body :: Eval m (Value (Eval m)) -> Eval m (Value (Eval m))
      body v = Eval $ \ toph topk ->
        let cs' = map (\ (p, e) -> (p, \ p' -> go (foldl' (:>) env p') e)) cs
            (es, vs) = partitionEithers (map (\case{ (PEff e, b) -> Left (e, b) ; (PVal v, b) -> Right (v, b) }) cs')
            -- run the effect handling cases
            h op = foldr (\ (p, b) rest -> maybe rest (runEval h k . b . fmap pure . PEff) (matchE p op)) (toph op) es
            -- run the value handling cases
            k v = runEval toph topk $ force env v >>= \ v' -> foldr (\ (p, b) rest -> maybe rest (b . fmap pure . PVal) (matchV p v')) (error "non-exhaustive patterns in lambda") vs
        in runEval h k v
    XApp  f a        -> do
      f' <- go env f
      app f' (go env a)
    XThunk b         -> pure $ VThunk (go env b)
    XForce t         -> go env t >>= (`app` pure unit)
    XCon n _ fs      -> VCon n <$> traverse (go env) fs
    XString s        -> pure $ VString s
    XOp n _ sp       -> do
      sp' <- traverse (go env) sp
      -- FIXME: should we really discard the contintinuation here?
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

data Op m a = Op (Q Name) (Stack (Value m)) (Value m -> m a)

type Handler r m a = Op (Eval m) a -> m r

runEval :: Handler r m a -> (a -> m r) -> Eval m a -> m r
runEval hdl k (Eval m) = m hdl k

newtype Eval m a = Eval (forall r . Handler r m a -> (a -> m r) -> m r)

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

data Value m
  = VLam [Pattern Name] (m (Value m) -> m (Value m))
  | VNe (Var Void Level) (Stack (m (Value m)))
  -- fixme: should we represent thunks & forcing explicitly?
  | VThunk (m (Value m))
  -- fixme: should these be computations too?
  | VOp (Q Name) (Stack (Value m)) (Value m)
  | VCon (Q Name) (Stack (Value m))
  | VString Text

unit :: Value m
unit = VCon (["Data", "Unit"] :.: U "unit") Nil


-- Elimination

matchE :: Monad m => EffectPattern Name -> Op m (Value m) -> Maybe (EffectPattern (Value m))
matchE (POp n ps _) (Op n' fs k) = POp n' <$ guard (n == n') <*> zipWithM matchV ps fs <*> pure (VLam [PVal (PVar __)] (k =<<))

matchV :: ValuePattern Name -> Value m -> Maybe (ValuePattern (Value m))
matchV p s = case p of
  PWildcard -> pure PWildcard
  PVar _    -> pure (PVar s)
  PCon n ps
    | VCon n' fs <- s -> PCon n' <$ guard (n == n') <*> zipWithM matchV ps fs
  PCon{}    -> empty


-- Quotation

quoteV :: Monad m => Level -> Value m -> m Expr
quoteV d = \case
  VLam ps b  -> XLam <$> traverse (\ p -> (p,) <$> let (d', p') = fill (\ d -> (succ d, VNe (Free d) Nil)) d p in quoteV d' =<< b (pure (constructP p'))) ps
  VThunk b   -> XThunk <$> (quoteV d =<< b)
  VNe h sp   -> foldl' XApp (XVar (levelToIndex d <$> h)) <$> traverse (quoteV d =<<) sp
  VOp q fs k -> XApp <$> quoteV d k <*> (XOp q Nil <$> traverse (quoteV d) fs)
  VCon n fs  -> XCon n Nil <$> traverse (quoteV d) fs
  VString s  -> pure $ XString s


constructP :: Pattern (Value m) -> Value m
constructP = \case
  PVal v -> constructV v
  PEff e -> constructE e

constructV :: ValuePattern (Value m) -> Value m
constructV = \case
  PWildcard -> VString "wildcard" -- FIXME: maybe should provide a variable here anyway?
  PVar v    -> v
  PCon q fs -> VCon q (constructV <$> fs)

constructE :: EffectPattern (Value m) -> Value m
constructE (POp q fs k) = VOp q (constructV <$> fs) k
