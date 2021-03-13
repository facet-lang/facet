{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Eval
( -- * Evaluation
  eval
, force
  -- * Machinery
, Handler
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

eval :: forall m sig . (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Snoc (Value m) -> Snoc (QName, Handler m) -> Expr -> ContT (Value m) m (Value m)
eval env hdl = \case
  XVar (Global n) -> global n
  XVar (Free v)   -> var env v
  XTLam b         -> tlam (eval env hdl b)
  XInst f t       -> inst (eval env hdl f) t
  XLam cs         -> lam env hdl (map (fmap (\ e env -> eval env hdl e)) cs)
  XApp  f a       -> app env hdl (eval env hdl f) a
  XCon n _ fs     -> con n (eval env hdl <$> fs)
  XString s       -> string s
  XOp n _ sp      -> op n (eval env hdl <$> sp)

global :: QName -> ContT (Value m) m (Value m)
global n = pure $ VNe (Global n) Nil

var :: HasCallStack => Snoc (Value m) -> Index -> ContT (Value m) m (Value m)
var env v = pure (env ! getIndex v)

tlam :: ContT (Value m) m (Value m) -> ContT (Value m) m (Value m)
tlam = id

inst :: ContT (Value m) m (Value m) -> TExpr -> ContT (Value m) m (Value m)
inst = const

lam :: (HasCallStack, Applicative m) => Snoc (Value m) -> Snoc (QName, Handler m) -> [(Pattern Name, Snoc (Value m) -> ContT (Value m) m (Value m))] -> ContT (Value m) m (Value m)
lam env hdl cs = pure $ VLam (map fst cs) (h env) (k env)
  where
  (es, vs) = partitionEithers (map (\case{ (PEff e, b) -> Left (e, b) ; (PVal v, b) -> Right (v, b) }) cs)
  h env = foldl' (\ prev (POp n ps _, b) -> prev :> (n, \ sp k -> runContT (b (bindSpine env ps sp :> VLam [pvar __] Nil k)) pure)) hdl es
  k env v = maybe (error "non-exhaustive patterns in lambda") (`runContT` pure) (foldMapA (\ (p, b) -> b . (env <>) <$> matchV p v) vs)

app :: (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Snoc (Value m) -> Snoc (QName, Handler m) -> ContT (Value m) m (Value m) -> Expr -> ContT (Value m) m (Value m)
app env hdl f a = do
  f' <- f
  case f' of
    VLam _ h k -> eval env h a >>= force env hdl >>= lift . k
    VNe v sp   -> pure $ VNe v (sp :> a)
    VOp n _    -> fail $ "expected lambda, got op "     <> show n
    VCon n _   -> fail $ "expected lambda, got con "    <> show n
    VString s  -> fail $ "expected lambda, got string " <> show s

string :: Text -> ContT (Value m) m (Value m)
string = pure . VString

con :: QName -> Snoc (ContT (Value m) m (Value m)) -> ContT (Value m) m (Value m)
con n fs = VCon n <$> sequenceA fs

-- FIXME: I think this subverts scoped operations: we evaluate the arguments before the handler has had a chance to intervene. this doesn’t explain why it behaves the same when we use an explicit suspended computation, however.
op :: QName -> Snoc (ContT (Value m) m (Value m)) -> ContT (Value m) m (Value m)
op n sp = do
  sp' <- sequenceA sp
  pure $ VOp n sp'


-- | Hereditary substitution on values.
force :: (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Snoc (Value m) -> Snoc (QName, Handler m) -> Value m -> ContT (Value m) m (Value m)
force env hdl = \case
  VNe (Global h) sp -> foldl' (\ f a -> force env hdl =<< app env hdl f a) (eval env hdl =<< resolve h) sp
  VOp n sp          -> ContT $ \ k -> maybe (fail ("unhandled operation: " <> show n)) (\ (_, h) -> h sp k) (find ((n ==) . fst) hdl)
  v                 -> pure v

resolve :: Has (Reader Graph :+: Reader Module) sig m => QName -> ContT (Value m) m Expr
resolve n = do
  mod <- lift ask
  graph <- lift ask
  case lookupQ graph mod n of
    Just (_ :=: Just (DTerm v) ::: _) -> pure v -- FIXME: store values in the module graph
    _                                 -> error "throw a real error here"


-- Machinery

type Handler m = Snoc (Value m) -> (Value m -> m (Value m)) -> m (Value m)


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
  PEff (POp q fs _) -> maybe (error ("unhandled operation: " <> show q)) (\ (_, h) -> h (constructV <$> fs) pure) (find ((== q) . fst) h)
  where
  (d', p') = fill ((,) <$> succ <*> (`VNe` Nil) . Free) d p


constructV :: ValuePattern (Value m) -> Value m
constructV = \case
  PWildcard -> unit -- FIXME: maybe should provide a variable here anyway?
  PVar v    -> v
  PCon q fs -> VCon q (constructV <$> fs)
