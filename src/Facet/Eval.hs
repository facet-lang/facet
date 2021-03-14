{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Eval
( -- * Evaluation
  eval
, force
  -- * Machinery
, Handler(..)
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
import Control.Monad (ap, guard, join, liftM)
import Control.Monad.Trans.Class
import Data.Either (partitionEithers)
import Data.Foldable
import Data.Function
import Data.Maybe (fromMaybe)
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

eval :: forall m sig . (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Snoc (Value (Eval m)) -> Snoc (QName, Handler (Eval m)) -> Expr -> Eval m (Value (Eval m))
eval env hdl = \case
  XVar (Global n) -> global n
  XVar (Free v)   -> var env v
  XTLam b         -> tlam (eval env hdl b)
  XInst f t       -> inst (eval env hdl f) t
  XLam cs         -> lam (map (fmap (\ e vs -> eval (env <> vs) hdl e)) cs)
  XApp  f a       -> app hdl (eval env hdl f) (\ hdl -> eval env hdl a)
  XCon n _ fs     -> con n (eval env hdl <$> fs)
  XString s       -> string s
  XOp n _ sp      -> op n (eval env hdl <$> sp)

global :: QName -> Eval m (Value (Eval m))
global n = pure $ VNe (Global n) Nil

var :: (HasCallStack, Applicative m) => Snoc (Value m) -> Index -> m (Value m)
var env v = pure (env ! getIndex v)

tlam :: Eval m (Value (Eval m)) -> Eval m (Value (Eval m))
tlam = id

inst :: Eval m (Value (Eval m)) -> TExpr -> Eval m (Value (Eval m))
inst = const

lam :: HasCallStack => [(Pattern Name, Snoc (Value (Eval m)) -> Eval m (Value (Eval m)))] -> Eval m (Value (Eval m))
lam cs = pure $ VLam (map fst cs) h k
  where
  (es, vs) = partitionEithers (map (\case{ (PEff e, b) -> Left (e, b) ; (PVal v, b) -> Right (v, b) }) cs)
  h = foldl' (\ prev (POp n ps _, b) -> prev :> (n, Handler $ \ sp k -> b (bindSpine Nil ps sp :> VLam [pvar __] Nil k))) Nil es
  k v = fromMaybe (error "non-exhaustive patterns in lambda") (foldMapA (\ (p, b) -> matchV b p v) vs)

app :: MonadFail m => Snoc (QName, Handler (Eval m)) -> Eval m (Value (Eval m)) -> (Snoc (QName, Handler (Eval m)) -> Eval m (Value (Eval m))) -> Eval m (Value (Eval m))
app hdl f a = do
  f' <- f
  case f' of
    VLam _ h k -> a (hdl <> h) >>= k
    VNe v sp   -> pure $ VNe v (sp :> a)
    VOp n _    -> fail $ "expected lambda, got op "     <> show n
    VCon n _   -> fail $ "expected lambda, got con "    <> show n
    VString s  -> fail $ "expected lambda, got string " <> show s

string :: Text -> Eval m (Value (Eval m))
string = pure . VString

con :: QName -> Snoc (Eval m (Value (Eval m))) -> Eval m (Value (Eval m))
con n fs = VCon n <$> sequenceA fs

-- FIXME: I think this subverts scoped operations: we evaluate the arguments before the handler has had a chance to intervene. this doesn’t explain why it behaves the same when we use an explicit suspended computation, however.
op :: QName -> Snoc (Eval m (Value (Eval m))) -> Eval m (Value (Eval m))
op n sp = VOp n <$> sequenceA sp


-- | Hereditary substitution on values.
force :: (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Snoc (Value (Eval m)) -> Snoc (QName, Handler (Eval m)) -> Value (Eval m) -> Eval m (Value (Eval m))
force env hdl = \case
  VNe (Global h) sp -> foldl' (\ f a -> force env hdl =<< app hdl f (\ hdl -> force env hdl =<< a hdl)) (eval env hdl =<< resolve h) sp
  VOp n sp          -> Eval $ \ k -> maybe (fail ("unhandled operation: " <> show n)) (\ (_, h) -> runEval (runHandler h sp pure) k) (find ((n ==) . fst) hdl)
  v                 -> pure v

resolve :: Has (Reader Graph :+: Reader Module) sig m => QName -> Eval m Expr
resolve n = do
  mod <- lift ask
  graph <- lift ask
  case lookupQ graph mod n of
    Just (_ :=: Just (DTerm v) ::: _) -> pure v -- FIXME: store values in the module graph
    _                                 -> error "throw a real error here"


-- Machinery

newtype Handler m = Handler { runHandler :: Snoc (Value m) -> (Value m -> m (Value m)) -> m (Value m) }

newtype Eval m a = Eval { runEval :: forall r . (a -> m r) -> m r }

instance Functor (Eval m) where
  fmap = liftM

instance Applicative (Eval m) where
  pure a = Eval $ \ k -> k a
  (<*>) = ap

instance Monad (Eval m) where
  m >>= f = Eval $ \ k -> runEval m (\ a -> runEval (f a) k)

instance MonadFail m => MonadFail (Eval m) where
  fail = lift . fail

instance MonadTrans Eval where
  lift m = Eval $ \ k -> m >>= k

instance Algebra sig m => Algebra sig (Eval m) where
  alg hdl sig ctx = Eval $ \ k -> alg (\ m -> runEval (hdl m) pure) sig ctx >>= k


-- Values

data Value m
  -- | Neutral; variables, only used during quotation
  = VNe (Var Level) (Snoc (Snoc (QName, Handler m) -> m (Value m)))
  -- | Neutral; effect operations, only used during quotation.
  | VOp QName (Snoc (Value m))
  -- | Value; data constructors.
  | VCon QName (Snoc (Value m))
  -- | Value; strings.
  | VString Text
  -- | Computation; lambdas.
  | VLam [Pattern Name] (Snoc (QName, Handler m)) (Value m -> m (Value m))

unit :: Value m
unit = VCon (["Data", "Unit"] :.: U "unit") Nil


-- Elimination

matchV :: (Snoc (Value m) -> a) -> ValuePattern Name -> Value m -> Maybe a
matchV k p s = case p of
  PWildcard -> pure (k Nil)
  PVar _    -> pure (k (Nil :> s))
  PCon n ps
    | VCon n' fs <- s -> k . join <$ guard (n == n') <*> zipWithM (matchV id) ps fs
  PCon{}    -> empty

bindValue ::  Snoc (Value m) -> ValuePattern Name -> Value m -> Snoc (Value m)
bindValue env PWildcard   _           = env
bindValue env (PVar _)    v           = env :> v
bindValue env (PCon _ ps) (VCon _ fs) = bindSpine env ps fs
bindValue env _           _           = env -- FIXME: probably not a good idea to fail silently

bindSpine :: Snoc (Value m) -> Snoc (ValuePattern Name) -> Snoc (Value m) -> Snoc (Value m)
bindSpine env Nil        Nil        = env
bindSpine env (tp :> hp) (ts :> hs) = bindValue (bindSpine env tp ts) hp hs
bindSpine env _          _          = env -- FIXME: probably not a good idea to fail silently


-- Quotation

quoteV :: Monad m => Level -> Value m -> m Expr
quoteV d = \case
  VLam ps h k -> XLam <$> traverse (quoteClause d h k) ps
  VNe v sp    -> foldl' XApp (XVar (levelToIndex d <$> v)) <$> traverse (\ a -> quoteV d =<< a Nil) sp
  VOp q fs    -> XOp  q Nil <$> traverse (quoteV d) fs
  VCon n fs   -> XCon n Nil <$> traverse (quoteV d) fs
  VString s   -> pure $ XString s

quoteClause :: Monad m => Level -> Snoc (QName, Handler m) -> (Value m -> m (Value m)) -> Pattern Name -> m (Pattern Name, Expr)
quoteClause d h k p = fmap (p,) . quoteV d' =<< case p' of
  PVal p'           -> k (constructV p')
  PEff (POp q fs _) -> maybe (error ("unhandled operation: " <> show q)) (\ (_, h) -> runHandler h (constructV <$> fs) pure) (find ((== q) . fst) h)
  where
  (d', p') = fill ((,) <$> succ <*> (`VNe` Nil) . Free) d p


constructV :: ValuePattern (Value m) -> Value m
constructV = \case
  PWildcard -> unit -- FIXME: maybe should provide a variable here anyway?
  PVar v    -> v
  PCon q fs -> VCon q (constructV <$> fs)
