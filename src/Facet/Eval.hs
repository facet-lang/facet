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
import Control.Monad (guard, join)
import Control.Monad.Trans.Class
import Control.Monad.Trans.Cont
import Data.Either (partitionEithers)
import Data.Foldable
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

eval :: forall m sig . (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Expr -> Eval m (Value m)
eval = \case
  XVar (Global n) -> global n
  XVar (Free v)   -> var v
  XTLam b         -> tlam (eval b)
  XInst f t       -> inst (eval f) t
  XLam cs         -> lam (map (fmap (\ e env -> withEnv env (eval e))) cs)
  XApp  f a       -> app (eval f) a
  XCon n _ fs     -> con n (eval <$> fs)
  XString s       -> string s
  XOp n _ sp      -> op n (eval <$> sp)

global :: QName -> Eval m (Value m)
global n = pure $ VNe (Global n) Nil

var :: HasCallStack => Index -> Eval m (Value m)
var v = Eval $ \ env _ k -> k (env ! getIndex v)

tlam :: Eval m (Value m) -> Eval m (Value m)
tlam = id

inst :: Eval m (Value m) -> TExpr -> Eval m (Value m)
inst = const

lam :: (HasCallStack, Applicative m) => [(Pattern Name, Snoc (Value m) -> Eval m (Value m))] -> Eval m (Value m)
lam cs = Eval $ \ env hdl k' -> k' $ VLam (map fst cs) (h env hdl) (k env hdl)
  where
  (es, vs) = partitionEithers (map (\case{ (PEff e, b) -> Left (e, b) ; (PVal v, b) -> Right (v, b) }) cs)
  h env hdl = foldl' (\ prev (POp n ps _, b) -> prev :> (n, Handler $ \ sp k -> runEval (b (bindSpine env ps sp :> VLam [pvar __] Nil k)) env hdl pure)) hdl es
  k env hdl v = maybe (error "non-exhaustive patterns in lambda") (\ m -> runEval m env hdl pure) (foldMapA (\ (p, b) -> b . (env <>) <$> matchV p v) vs)

app :: (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Eval m (Value m) -> Expr -> Eval m (Value m)
app f a = do
  f' <- f
  case f' of
    VLam _ h k -> withHandlers h (eval a >>= force) >>= lift . k
    VNe v sp   -> pure $ VNe v (sp :> a)
    VOp n _    -> fail $ "expected lambda, got op "     <> show n
    VCon n _   -> fail $ "expected lambda, got con "    <> show n
    VString s  -> fail $ "expected lambda, got string " <> show s

string :: Text -> Eval m (Value m)
string = pure . VString

con :: QName -> Snoc (Eval m (Value m)) -> Eval m (Value m)
con n fs = VCon n <$> sequenceA fs

-- FIXME: I think this subverts scoped operations: we evaluate the arguments before the handler has had a chance to intervene. this doesn’t explain why it behaves the same when we use an explicit suspended computation, however.
op :: QName -> Snoc (Eval m (Value m)) -> Eval m (Value m)
op n sp = VOp n <$> sequenceA sp


-- | Hereditary substitution on values.
force :: (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Value m -> Eval m (Value m)
force = \case
  VNe (Global h) sp -> foldl' (\ f a -> force =<< app f a) (eval =<< resolve h) sp
  VOp n sp          -> Eval $ \ _ hdl k -> maybe (fail ("unhandled operation: " <> show n)) (\ (_, h) -> runHandler h sp k) (find ((n ==) . fst) hdl)
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

withEnv :: Snoc (Value m) -> Eval m a -> Eval m a
withEnv env m = Eval $ \ _ -> runEval m env

withHandlers :: Snoc (QName, Handler m) -> Eval m a -> Eval m a
withHandlers hdl m = Eval $ \ env _ -> runEval m env hdl

newtype Eval m a = Eval { runEval :: Snoc (Value m) -> Snoc (QName, Handler m) -> (a -> m (Value m)) -> m (Value m) }
  deriving (Applicative, Functor, Monad, MonadFail) via ReaderC (Snoc (Value m)) (ReaderC (Snoc (QName, Handler m)) (ContT (Value m) m))

instance MonadTrans Eval where
  lift m = Eval $ \ _ _ k -> m >>= k


-- Values

data Value m
  -- | Neutral; variables, only used during quotation
  = VNe (Var Level) (Snoc Expr)
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

matchV :: ValuePattern Name -> Value m -> Maybe (Snoc (Value m))
matchV p s = case p of
  PWildcard -> pure Nil
  PVar _    -> pure (Nil :> s)
  PCon n ps
    | VCon n' fs <- s -> join <$ guard (n == n') <*> zipWithM matchV ps fs
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
  VNe v sp    -> pure $ foldl' XApp (XVar (levelToIndex d <$> v)) sp
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
