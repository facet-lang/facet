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

eval :: forall m sig . (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Snoc (Value (Eval m)) -> Snoc (QName, Snoc (Value (Eval m)) -> (Value (Eval m) -> Eval m (Value (Eval m))) -> Eval m (Value (Eval m))) -> Expr -> Eval m (Value (Eval m))
eval env hdl = \case
  XVar (Global n)  -> global n >>= eval env hdl
  XVar (Free v)    -> var env v
  XVar (Metavar m) -> case m of {}
  XTLam b          -> tlam (eval env hdl b)
  XInst f t        -> inst (eval env hdl f) t
  XLam cs          -> lam env (map (fmap (\ e env -> eval env hdl e)) cs)
  XApp  f a        -> app (eval env hdl f) (eval env hdl a)
  XCon n _ fs      -> con n (eval env hdl <$> fs)
  XString s        -> string s
  XOp n _ sp       -> op n (eval env hdl <$> sp)

global :: Has (Reader Graph :+: Reader Module) sig m => QName -> Eval m Expr
global n = do
  mod <- ask
  graph <- ask
  case lookupQ graph mod n of
    Just (_ :=: Just (DTerm v) ::: _) -> pure v -- FIXME: store values in the module graph
    _                                 -> error "throw a real error here"

var :: HasCallStack => Snoc (Value (Eval m)) -> Index -> Eval m (Value (Eval m))
var env v = pure (env ! getIndex v)

tlam :: Eval m (Value (Eval m)) -> Eval m (Value (Eval m))
tlam = id

inst :: Eval m (Value (Eval m)) -> TExpr -> Eval m (Value (Eval m))
inst = const

lam :: HasCallStack => Snoc (Value (Eval m)) -> [(Pattern Name, Snoc (Value (Eval m)) -> Eval m (Value (Eval m)))] -> Eval m (Value (Eval m))
lam env cs = do
  pure $ VLam (map fst cs) (h env) (k env)
  where
  (es, vs) = partitionEithers (map (\case{ (PEff e, b) -> Left (e, b) ; (PVal v, b) -> Right (v, b) }) cs)
  h env = foldl' (\ prev (POp n ps _, b) -> prev :> (n, \ sp k -> b (bindSpine env ps sp :> VLam [pvar __] Nil k))) Nil es
  k env v = fromMaybe (error "non-exhaustive patterns in lambda") (foldMapA (\ (p, b) -> matchV (b . (env <>)) p v) vs)

app :: MonadFail m => Eval m (Value (Eval m)) -> Eval m (Value (Eval m)) -> Eval m (Value (Eval m))
app f (Eval a) = do
  VLam _ h k <- f
  Eval (a . (<> h)) >>= k

string :: Text -> Eval m (Value (Eval m))
string = pure . VString

con :: QName -> Snoc (Eval m (Value (Eval m))) -> Eval m (Value (Eval m))
con n fs = VCon n <$> sequenceA fs

-- FIXME: I think this subverts scoped operations: we evaluate the arguments before the handler has had a chance to intervene. this doesn’t explain why it behaves the same when we use an explicit suspended computation, however.
op :: MonadFail m => QName -> Snoc (Eval m (Value (Eval m))) -> Eval m (Value (Eval m))
op n sp = do
  sp' <- sequenceA sp
  Eval $ \ h k -> maybe (fail ("unhandled operation: " <> show n)) (\ (_, h') -> runEval h k (h' sp' pure)) (find ((n ==) . fst) h)


-- Machinery

data Op a = Op QName (Snoc a)

type Handler m = Snoc (Value m) -> (Value m -> m (Value m)) -> m (Value m)

runEval :: Snoc (QName, Handler (Eval m)) -> (a -> m r) -> Eval m a -> m r
runEval hdl k (Eval m) = m hdl k

newtype Eval m a = Eval (forall r . Snoc (QName, Handler (Eval m)) -> (a -> m r) -> m r)

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
  VLam ps h k     -> XLam <$> traverse (quoteClause d h k) ps
  VFree lvl       -> pure (XVar (Free (levelToIndex d lvl)))
  VOp (Op q fs) k -> XApp <$> quoteV d k <*> (XOp q Nil <$> traverse (quoteV d) fs)
  VCon n fs       -> XCon n Nil <$> traverse (quoteV d) fs
  VString s       -> pure $ XString s

quoteClause :: Monad m => Level -> Snoc (QName, Handler m) -> (Value m -> m (Value m)) -> Pattern Name -> m (Pattern Name, Expr)
quoteClause d h k p = fmap (p,) . quoteV d' =<< case p' of
  PVal p'           -> k (constructV p')
  PEff (POp q fs _) -> maybe (error ("unhandled operation: " <> show q)) (\ (_, h) -> h (constructV <$> fs) pure) (find ((== q) . fst) h)
  where
  (d', p') = fill ((,) <$> succ <*> VFree) d p


constructV :: ValuePattern (Value m) -> Value m
constructV = \case
  PWildcard -> unit -- FIXME: maybe should provide a variable here anyway?
  PVar v    -> v
  PCon q fs -> VCon q (constructV <$> fs)
