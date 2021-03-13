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
import Control.Effect.NonDet (foldMapA)
import Control.Monad (ap, guard, liftM)
import Control.Monad.Trans.Class
import Data.Either (partitionEithers)
import Data.Foldable (foldl')
import Data.Function
import Data.Text (Text)
import Facet.Core.Module
import Facet.Core.Term
import Facet.Core.Type (TExpr)
import Facet.Graph
import Facet.Name hiding (Op)
import Facet.Semialign (zipWithM)
import Facet.Snoc
import Facet.Syntax
import GHC.Stack (HasCallStack)
import Prelude hiding (zipWith)

eval :: forall m sig . (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Expr -> Eval m (Value (Eval m))
eval = \case
  XVar (Global n)  -> global n >>= eval
  XVar (Free v)    -> var v
  XVar (Metavar m) -> case m of {}
  XTLam b          -> tlam (eval b)
  XInst f t        -> inst (eval f) t
  XLam cs          -> do
    env <- askEnv
    lam (map (fmap (\ e vs -> withEnv (env <> vs) (eval e))) cs)
  XApp  f a        -> app (eval f) (eval a)
  XCon n _ fs      -> con n (eval <$> fs)
  XString s        -> string s
  XOp n _ sp       -> op n (eval <$> sp)

global :: Has (Reader Graph :+: Reader Module) sig m => QName -> Eval m Expr
global n = do
  mod <- ask
  graph <- ask
  case lookupQ graph mod n of
    Just (_ :=: Just (DTerm v) ::: _) -> pure v -- FIXME: store values in the module graph
    _                                 -> error "throw a real error here"

var :: HasCallStack => Index -> Eval m (Value (Eval m))
var v = (! getIndex v) <$> askEnv

tlam :: Eval m (Value (Eval m)) -> Eval m (Value (Eval m))
tlam = id

inst :: Eval m (Value (Eval m)) -> TExpr -> Eval m (Value (Eval m))
inst = const

lam :: HasCallStack => [(Pattern Name, Snoc (Value (Eval m)) -> Eval m (Value (Eval m)))] -> Eval m (Value (Eval m))
lam cs = pure $ VLam (map fst cs) h k
  where
  (es, vs) = partitionEithers (map (\case{ (PEff e, b) -> Left (e, b) ; (PVal v, b) -> Right (v, b) }) cs)
  h op = foldMapA (\ (p, b) -> matchE (\ vs k -> b (foldl' (foldl' (:>)) Nil vs :> VLam [pvar __] (const Nothing) k)) p op) es
  k v = foldr (\ (p, b) rest -> maybe rest (b . foldl' (:>) Nil) (matchV p v)) (error "non-exhaustive patterns in lambda") vs

app :: MonadFail m => Eval m (Value (Eval m)) -> Eval m (Value (Eval m)) -> Eval m (Value (Eval m))
app f (Eval a) = do
  VLam _ h k <- f
  Eval (a . (:> h)) >>= k

string :: Text -> Eval m (Value (Eval m))
string = pure . VString

con :: QName -> Snoc (Eval m (Value (Eval m))) -> Eval m (Value (Eval m))
con n fs = VCon n <$> sequenceA fs

-- FIXME: I think this subverts scoped operations: we evaluate the arguments before the handler has had a chance to intervene. this doesn’t explain why it behaves the same when we use an explicit suspended computation, however.
op :: QName -> Snoc (Eval m (Value (Eval m))) -> Eval m (Value (Eval m))
op n sp = do
  sp' <- sequenceA sp
  Eval $ \ h k env -> runEval h k env (foldr (\ h rest -> maybe rest ($ pure) (h (Op n sp'))) (error ("unhandled operation: " <> show n)) h)


-- Machinery

data Op a = Op QName (Snoc a)

type Handler m = Op (Value m) -> Maybe ((Value m -> m (Value m)) -> m (Value m))

runEval :: Snoc (Handler (Eval m)) -> (a -> m r) -> Snoc (Value (Eval m)) -> Eval m a -> m r
runEval hdl k env (Eval m) = m hdl k env

askEnv :: Eval m (Snoc (Value (Eval m)))
askEnv = Eval $ \ _ k -> k

withEnv :: Snoc (Value (Eval m)) -> Eval m a -> Eval m a
withEnv e (Eval run) = Eval $ \ h k _ -> run h k e

newtype Eval m a = Eval (forall r . Snoc (Handler (Eval m)) -> (a -> m r) -> Snoc (Value (Eval m)) -> m r)

instance Functor (Eval m) where
  fmap = liftM

instance Applicative (Eval m) where
  pure a = Eval $ \ _ k _ -> k a
  (<*>) = ap

instance Monad (Eval m) where
  m >>= f = Eval $ \ hdl k env -> runEval hdl (runEval hdl k env . f) env m

instance MonadFail m => MonadFail (Eval m) where
  fail = lift . fail

instance MonadTrans Eval where
  lift m = Eval $ \ _ k _ -> m >>= k

instance Algebra sig m => Algebra sig (Eval m) where
  alg hdl sig ctx = Eval $ \ h k env -> alg (runEval h pure env . hdl) sig ctx >>= k


-- Values

data Value m
  -- | Neutral; variables, only used during quotation
  = VFree Level
  -- | Neutral; effect operations, only used during quotation.
  | VOp (Op (Value m)) (Value m)
  -- | Value; data constructors.
  | VCon QName (Snoc (Value m))
  -- | Value; strings.
  | VString Text
  -- | Computation; lambdas.
  | VLam [Pattern Name] (Handler m) (Value m -> m (Value m))

unit :: Value m
unit = VCon (["Data", "Unit"] :.: U "unit") Nil


-- Elimination

matchE :: (Snoc (ValuePattern (Value m)) -> a) -> EffectPattern Name -> Op (Value m) -> Maybe a
matchE k (POp n ps _) (Op n' fs) = k <$ guard (n == n') <*> zipWithM matchV ps fs

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
  VFree lvl       -> pure (XVar (Free (levelToIndex d lvl)))
  VOp (Op q fs) k -> XApp <$> quoteV d k <*> (XOp q Nil <$> traverse (quoteV d) fs)
  VCon n fs       -> XCon n Nil <$> traverse (quoteV d) fs
  VString s       -> pure $ XString s

quoteClause :: Monad m => Level -> Handler m -> (Value m -> m (Value m)) -> Pattern Name -> m (Pattern Name, Expr)
quoteClause d h k p = fmap (p,) . quoteV d' =<< case p' of
  PVal p'           -> k (constructV p')
  PEff (POp q fs _) -> maybe (error ("unhandled operation: " <> show q)) ($ pure) (h (Op q (constructV <$> fs)))
  where
  (d', p') = fill ((,) <$> succ <*> VFree) d p


constructV :: ValuePattern (Value m) -> Value m
constructV = \case
  PWildcard -> unit -- FIXME: maybe should provide a variable here anyway?
  PVar v    -> v
  PCon q fs -> VCon q (constructV <$> fs)
