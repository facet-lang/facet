{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Eval
( -- * Evaluation
  eval
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
import Control.Monad (ap, guard, join, liftM, (>=>))
import Control.Monad.Trans.Class
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

eval :: (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Snoc (Value (Eval m)) -> Snoc (RName, Handler (Eval m)) -> Expr -> Eval m (Value (Eval m))
eval env hdl = \case
  XVar (Global n) -> global n >>= eval env hdl
  XVar (Free v)   -> var env v
  XTLam b         -> tlam (eval env hdl b)
  XInst f t       -> inst (eval env hdl f) t
  XLam cs         -> lam env cs
  XApp  f a       -> app env hdl (eval env hdl f) a
  XCon n _ fs     -> con n (eval env hdl <$> fs)
  XString s       -> string s
  XOp n _ sp      -> op hdl n (flip (eval env) <$> sp)
  XThunk t        -> thunk env t
  XForce t        -> force hdl (eval env hdl t)

global :: Has (Reader Graph :+: Reader Module) sig m => RName -> Eval m Expr
global n = do
  mod <- lift ask
  graph <- lift ask
  case lookupQ graph mod (toQ n) of
    Just (_ :=: Just (DTerm v) ::: _) -> pure v -- FIXME: store values in the module graph
    _                                 -> error "throw a real error here"

var :: (HasCallStack, Applicative m) => Snoc (Value m) -> Index -> m (Value m)
var env v = pure (env ! getIndex v)

tlam :: Eval m (Value (Eval m)) -> Eval m (Value (Eval m))
tlam = id

inst :: Eval m (Value (Eval m)) -> TExpr -> Eval m (Value (Eval m))
inst = const

lam :: Snoc (Value (Eval m)) -> [(Pattern Name, Expr)] -> Eval m (Value (Eval m))
lam env cs = pure $ VLam env cs

app :: (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Snoc (Value (Eval m)) -> Snoc (RName, Handler (Eval m)) -> Eval m (Value (Eval m)) -> Expr -> Eval m (Value (Eval m))
app envCallSite hdl f a = f >>= \case
  VLam env cs -> do
    let (h, k) = foldl' combine (Nil, const (error "non-exhaustive patterns in lambda")) cs
        combine (es, vs) = \case
          (PEff (POp n ps _), b) -> (es :> (n, Handler $ \ sp k -> traverse ($ (hdl <> h)) sp >>= \ sp -> eval (bindSpine env ps sp :> VCont k) hdl b), vs)
          (PEff (PAll _), b)     -> (es, \ a -> eval (env :> VThunk envCallSite a) hdl b)
          (PVal p, b)            -> (es, eval envCallSite (hdl <> h) >=> \ v -> fromMaybe (vs a) (matchV (\ vs -> eval (env <> vs) hdl b) p v))
    k a
  VCont k     -> k =<< eval envCallSite hdl a
  _           -> fail "expected lambda/continuation"

string :: Text -> Eval m (Value (Eval m))
string = pure . VString

con :: RName -> Snoc (Eval m (Value (Eval m))) -> Eval m (Value (Eval m))
con n fs = VCon n <$> sequenceA fs

-- FIXME: I think this subverts scoped operations: we evaluate the arguments before the handler has had a chance to intervene. this doesn’t explain why it behaves the same when we use an explicit suspended computation, however.
op :: MonadFail m => Snoc (RName, Handler (Eval m)) -> RName -> Snoc (Snoc (RName, Handler (Eval m)) -> Eval m (Value (Eval m))) -> Eval m (Value (Eval m))
op hdl n sp = Eval $ \ k -> maybe (fail ("unhandled operation: " <> show n)) (\ (_, h) -> runEval (runHandler h sp pure) k) (find ((n ==) . fst) hdl)

thunk :: Applicative m => Snoc (Value n) -> Expr -> m (Value n)
thunk env t = pure $ VThunk env t

force :: (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Snoc (RName, Handler (Eval m)) -> Eval m (Value (Eval m)) -> Eval m (Value (Eval m))
force hdl t = t >>= \case
  VThunk env c -> eval env hdl c
  _            -> fail "expected thunk"


-- Machinery

newtype Handler m = Handler { runHandler :: Snoc (Snoc (RName, Handler m) -> m (Value m)) -> (Value m -> m (Value m)) -> m (Value m) }

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
  = VVar (Var Level)
  -- | Value; data constructors.
  | VCon RName (Snoc (Value m))
  -- | Value; strings.
  | VString Text
  -- | Value; thunks.
  | VThunk (Snoc (Value m)) Expr
  -- | Computation; lambdas.
  | VLam (Snoc (Value m)) [(Pattern Name, Expr)]
  -- | Computation; continuations, used in effect handlers.
  | VCont (Value m -> m (Value m))

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
  VLam _ cs  -> pure $ XLam cs
  VCont k    -> quoteV (succ d) =<< k (VVar (Free d))
  VVar v     -> pure (XVar (levelToIndex d <$> v))
  VCon n fs  -> XCon n Nil <$> traverse (quoteV d) fs
  VString s  -> pure $ XString s
  VThunk _ t -> pure $ XThunk t
