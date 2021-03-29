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
import Control.Carrier.Reader
import Control.Monad (ap, guard, liftM, (>=>))
import Control.Monad.Trans.Class
import Data.Bifunctor (first)
import Data.Foldable
import Data.Function
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Facet.Core.Module
import Facet.Core.Pattern
import Facet.Core.Term
import Facet.Core.Type (TExpr)
import Facet.Env as Env
import Facet.Graph
import Facet.Name hiding (Op)
import Facet.Semialign (zipWithM)
import Facet.Snoc
import Facet.Snoc.NonEmpty as NE hiding ((|>))
import Facet.Syntax
import GHC.Stack (HasCallStack)
import Prelude hiding (zipWith)

eval :: (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Env (Value (Eval m)) -> [(RName, Handler (Eval m))] -> Expr -> Eval m (Value (Eval m))
eval env hdl = \case
  XVar (Global n)    -> global n >>= eval env hdl
  XVar (Free (v, n)) -> var env v n
  XTLam b            -> tlam (eval env hdl b)
  XInst f t          -> inst (eval env hdl f) t
  XLam cs            -> lam env cs
  XApp  f a          -> app env hdl (eval env hdl f) a
  XCon n _ fs        -> con n (eval env hdl <$> fs)
  XString s          -> string s
  XOp n _ sp         -> op hdl n (flip (eval env) <$> sp)

global :: Has (Reader Graph :+: Reader Module) sig m => RName -> Eval m Expr
global n = do
  mod <- lift ask
  graph <- lift ask
  case lookupQ graph mod (toQ n) of
    [_ :=: DTerm (Just v) _] -> pure v -- FIXME: store values in the module graph
    _                        -> error "throw a real error here"

var :: (HasCallStack, Applicative m) => Env (Value m) -> Index -> Name -> m (Value m)
var env v n = pure (index env v n)

tlam :: Eval m (Value (Eval m)) -> Eval m (Value (Eval m))
tlam = id

inst :: Eval m (Value (Eval m)) -> TExpr -> Eval m (Value (Eval m))
inst = const

lam :: Env (Value (Eval m)) -> [(Pattern Name, Expr)] -> Eval m (Value (Eval m))
lam env cs = pure $ VLam env cs

app :: (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Env (Value (Eval m)) -> [(RName, Handler (Eval m))] -> Eval m (Value (Eval m)) -> Expr -> Eval m (Value (Eval m))
app envCallSite hdl f a = f >>= \case
  VLam env cs -> k a where
    (h, k) = foldl' (\ (es, vs) -> \case
      (PEff (POp n ps nk), b) -> ((n, Handler $ \ sp k -> traverse ($ (h <> hdl)) sp >>= \ sp -> eval (bindSpine env ps sp |> pvar (nk :=: VCont k)) hdl b) : es, vs)
      (PEff (PAll n), b)      -> (es, \ a -> eval (env |> pvar (n :=: VLam envCallSite [(pvar __, a)])) hdl b)
      (PVal p, b)             -> (es, eval envCallSite (h <> hdl) >=> fromMaybe (vs a) . matchV (\ vs -> eval (env |> PVal vs) hdl b) p)) ([], const (fail "non-exhaustive patterns in lambda")) cs
  VCont k     -> k =<< eval envCallSite hdl a
  _           -> fail "expected lambda/continuation"

string :: Text -> Eval m (Value (Eval m))
string = pure . VString

con :: RName -> Snoc (Eval m (Value (Eval m))) -> Eval m (Value (Eval m))
con n fs = VCon n <$> sequenceA fs

op :: MonadFail m => [(RName, Handler (Eval m))] -> RName -> Snoc ([(RName, Handler (Eval m))] -> Eval m (Value (Eval m))) -> Eval m (Value (Eval m))
op hdl n sp = Eval $ \ k -> maybe (fail ("unhandled operation: " <> show n)) (\ (_, h) -> runEval (runHandler h sp pure) k) (find ((n ==) . fst) hdl)


-- Machinery

newtype Handler m = Handler { runHandler :: Snoc ([(RName, Handler m)] -> m (Value m)) -> (Value m -> m (Value m)) -> m (Value m) }

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
  = VVar (Var (Level, Name))
  -- | Value; data constructors.
  | VCon RName (Snoc (Value m))
  -- | Value; strings.
  | VString Text
  -- | Computation; lambdas.
  | VLam (Env (Value m)) [(Pattern Name, Expr)]
  -- | Computation; continuations, used in effect handlers.
  | VCont (Value m -> m (Value m))

unit :: Value m
unit = VCon (NE.FromList ["Data", "Unit"] :.: U "unit") Nil


-- Elimination

matchV :: (ValuePattern (Name :=: Value m) -> a) -> ValuePattern Name -> Value m -> Maybe a
matchV k p s = case p of
  PWildcard -> pure (k PWildcard)
  PVar n    -> pure (k (PVar (n :=: s)))
  PCon n ps
    | VCon n' fs <- s -> k . PCon n' <$ guard (n == n') <*> zipWithM (matchV id) ps fs
  PCon{}    -> Nothing

bindValue ::  Env (Value m) -> ValuePattern Name -> Value m -> Env (Value m)
bindValue env PWildcard   _           = env
bindValue env (PVar n)    v           = env |> pvar (n :=: v)
bindValue env (PCon _ ps) (VCon _ fs) = bindSpine env ps fs
bindValue env _           _           = env -- FIXME: probably not a good idea to fail silently

bindSpine :: Env (Value m) -> Snoc (ValuePattern Name) -> Snoc (Value m) -> Env (Value m)
bindSpine env Nil        Nil        = env
bindSpine env (tp :> hp) (ts :> hs) = bindValue (bindSpine env tp ts) hp hs
bindSpine env _          _          = env -- FIXME: probably not a good idea to fail silently


-- Quotation

quoteV :: Monad m => Level -> Value m -> m Expr
quoteV d = \case
  VLam _ cs -> pure $ XLam cs
  VCont k   -> quoteV (succ d) =<< k (VVar (Free (d, __)))
  VVar v    -> pure (XVar (first (levelToIndex d) <$> v))
  VCon n fs -> XCon n Nil <$> traverse (quoteV d) fs
  VString s -> pure $ XString s
