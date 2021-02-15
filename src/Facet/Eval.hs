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
  -- * Quotation
, quoteV
) where

import Control.Algebra hiding (Handler)
import Control.Applicative (Alternative(..))
import Control.Carrier.Reader
import Control.Monad (ap, guard, liftM)
import Control.Monad.Trans.Class
import Data.Either (partitionEithers)
import Data.Foldable (foldl')
import Data.Function
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

eval :: forall m sig . (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Expr -> Eval m (Value (Eval m))
eval = runReader Nil . go
  where
  go :: Expr -> ReaderC (Stack (Value (Eval m))) (Eval m) (Value (Eval m))
  go = \case
    XVar (Global n)  -> do
      mod <- lift ask
      graph <- lift ask
      case lookupQ graph mod n of
        Just (_ :=: Just (DTerm v) ::: _) -> go v
        _                                 -> error "throw a real error here"
    XVar (Free v)    -> asks (! getIndex v)
    XVar (Metavar m) -> case m of {}
    XTLam b          -> go b
    XInst f _        -> go f
    XLam cs          -> do
      env <- ask
      let cs' = map (fmap (\ e p' -> runReader (foldl' (:>) env p') (go e))) cs
          (es, vs) = partitionEithers (map (\case{ (PEff e, b) -> Left (e, b) ; (PVal v, b) -> Right (v, b) }) cs')
      pure $ VLam
        (map fst cs)
        (\ toph op k -> foldr (\ (p, b) rest -> maybe rest (b . PEff) (matchE p op k)) (toph op k) es)
        (\ v -> foldr (\ (p, b) rest -> maybe rest (b . PVal) (matchV p v)) (error "non-exhaustive patterns in lambda") vs)
    XApp  f a        -> do
      VLam _ h k <- go f
      extendHandler h (go a) >>= lift . k
    XThunk b         -> asks (\ env -> VThunk (runReader env (go b)))
    XForce t         -> do
      VThunk b <- go t
      lift b
    XCon n _ fs      -> VCon n <$> traverse go fs
    XString s        -> pure $ VString s
    XOp n _ sp       -> do
      sp' <- traverse go sp
      lift $ Eval $ \ h k -> runEval h k (h (Op n sp') pure)
    where
    extendHandler ext m = ReaderC $ \ env -> do
      let Eval run = runReader env m
      Eval $ \ h -> run (ext h)


-- Machinery

data Op a = Op (Q Name) (Stack a)

type Handler m = Op (Value m) -> (Value m -> m (Value m)) -> m (Value m)

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
  -- | Neutral; effect operations, only used during quotation.
  | VOp (Op (Value m)) (Value m)
  -- | Value; thunks, wrapping computations.
  | VThunk (m (Value m))
  -- | Value; data constructors.
  | VCon (Q Name) (Stack (Value m))
  -- | Value; strings.
  | VString Text
  -- | Computation; lambdas.
  | VLam [Pattern Name] (Handler m -> Handler m) (Value m -> m (Value m))

unit :: Value m
unit = VCon (["Data", "Unit"] :.: U "unit") Nil


-- Elimination

matchE :: EffectPattern Name -> Op (Value m) -> (Value m -> m (Value m)) -> Maybe (EffectPattern (Value m))
matchE (POp n ps _) (Op n' fs) k = POp n' <$ guard (n == n') <*> zipWithM matchV ps fs <*> pure (VLam [PVal (PVar __)] id k)

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
  VLam ps h k     -> XLam <$> traverse (quoteClause d h k) ps
  VThunk b        -> XThunk <$> (quoteV d =<< b)
  VFree lvl       -> pure (XVar (Free (levelToIndex d lvl)))
  VOp (Op q fs) k -> XApp <$> quoteV d k <*> (XOp q Nil <$> traverse (quoteV d) fs)
  VCon n fs       -> XCon n Nil <$> traverse (quoteV d) fs
  VString s       -> pure $ XString s

quoteClause :: Monad m => Level -> (Handler m -> Handler m) -> (Value m -> m (Value m)) -> Pattern Name -> m (Pattern Name, Expr)
quoteClause d h k p = fmap (p,) . quoteV d' =<< case p' of
  PVal p'           -> k (constructV p')
  PEff (POp q fs k) -> h (\ op _ -> pure (VOp op k)) (Op q (constructV <$> fs)) pure
  where
  (d', p') = fill ((,) <$> succ <*> VFree) d p


constructV :: ValuePattern (Value m) -> Value m
constructV = \case
  PWildcard -> unit -- FIXME: maybe should provide a variable here anyway?
  PVar v    -> v
  PCon q fs -> VCon q (constructV <$> fs)
