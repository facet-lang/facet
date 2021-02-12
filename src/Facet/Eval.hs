{-# LANGUAGE OverloadedLists #-}
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
, unit
, Value'(..)
, Comp(..)
, creturn
, Elim(..)
, ($$)
  -- * Quotation
, quoteV
, quoteC
) where

import Control.Algebra
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

eval :: forall m sig . (HasCallStack, Has (Reader Graph :+: Reader Module) sig m) => (Op (Eval m) (Value (Eval m)) -> m (Value (Eval m))) -> Expr -> Eval m (Value (Eval m))
eval = \ hdl -> force hdl Nil <=< go hdl Nil
  where
  go hdl env = \case
    XVar (Global n)  -> pure $ VNe (Global n) Nil
    XVar (Free v)    -> env ! getIndex v
    XVar (Metavar m) -> case m of {}
    XTLam b          -> go hdl env b
    XInst f _        -> go hdl env f
    XLam cs          -> pure $ VLam (map fst cs) body
      where
      -- FIXME: it’s really uncomfortable that this takes computations to computations. function application fundamentally is, and should remain, value to computation. effect handling is different and should be applied disjointly.
      body :: Eval m (Value (Eval m)) -> Eval m (Value (Eval m))
      body v = Eval $ \ toph topk ->
        let cs' = map (\ (p, e) -> (p, \ p' -> go hdl (foldl' (:>) env p') e)) cs
            (es, vs) = partitionEithers (map (\case{ (PEff e, b) -> Left (e, b) ; (PVal v, b) -> Right (v, b) }) cs')
            -- run the effect handling cases
            h op = foldr (\ (p, b) rest -> maybe rest (runEval h k . b . fmap pure . PEff) (matchE p op)) (toph op) es
            -- run the value handling cases
            k v = runEval toph topk $ force hdl env v >>= \ v' -> foldr (\ (p, b) rest -> maybe rest (b . fmap pure . PVal) (matchV p v')) (error "non-exhaustive patterns in lambda") vs
        in runEval h k v
    XApp  f a        -> do
      f' <- go hdl env f
      app f' (go hdl env a)
    XThunk b         -> pure $ VThunk (go hdl env b)
    XForce t         -> go hdl env t >>= (`app` pure unit)
    XCon n _ fs      -> VCon n <$> traverse (go hdl env) fs
    XString s        -> pure $ VString s
    XOp n _ sp       -> do
      sp' <- traverse (go hdl env) sp
      Eval $ \ h _ -> h (Op n sp' pure)
  app f a = case f of
    VNe h sp -> pure $ VNe h (sp:>a)
    VLam _ b -> b a
    _        -> error "throw a real error (apply)"
  force hdl env = \case
    VNe n sp -> forceN hdl env n sp
    v        -> pure v
  forceN hdl env (Global n)  sp = forceGlobal hdl env n sp
  forceN _   _   (Free n)    sp = pure $ VNe (Free n) sp
  forceN _   _   (Metavar m) _  = case m of {}
  forceGlobal hdl env n sp = do
    mod <- lift ask
    graph <- lift ask
    case lookupQ graph mod n of
      Just (_ :=: Just (DTerm v) ::: _) -> do
        v' <- go hdl env v
        force hdl env =<< foldM app v' sp
      _                                 -> error "throw a real error here"


-- Machinery

data Op m a = Op (Q Name) (Stack (Value m)) (Value m -> m a)

runEval :: (Op (Eval m) a -> m r) -> (a -> m r) -> Eval m a -> m r
runEval hdl k (Eval m) = m hdl k

newtype Eval m a = Eval (forall r . (Op (Eval m) a -> m r) -> (a -> m r) -> m r)

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

data Value' m
  = VVar (Var Void Level)
  | VThunk' (m (Comp m))
  | VCon' (Q Name) (Stack (Value' m))
  | VString' Text

data Comp m
  = CLam [Pattern Name] (Value' m -> m (Comp m))
  | COp (Q Name) (Stack (Value' m)) (Comp m)
  | CNe (Value' m) (Stack (Elim m))
  | CLet (Comp m) (Value' m -> m (Comp m))

creturn :: Value' m -> Comp m
creturn v = CNe v Nil

data Elim m
  = EApp (Value' m)
  | EForce

($$) :: Applicative m => Comp m -> Elim m -> m (Comp m)
CLam _ f            $$ EApp a = f a
CNe (VThunk' b) Nil $$ EForce = b
CNe h sp            $$ e      = pure $ CNe h (sp :> e)
_                   $$ EForce = error "can’t force non-thunk/neutral comp"
_                   $$ EApp _ = error "can’t apply non-function/neutral comp"


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


quoteV' :: Monad m => Level -> Value' m -> m Expr
quoteV' d = \case
  VThunk' b  -> XThunk <$> (quoteC d =<< b)
  VVar h     -> pure $ XVar (levelToIndex d <$> h)
  VCon' n fs -> XCon n Nil <$> traverse (quoteV' d) fs
  VString' s -> pure $ XString s

quoteC :: Monad m => Level -> Comp m -> m Expr
quoteC d = \case
  CLam ps b  -> XLam <$> traverse (\ p -> (p,) <$> let (d', p') = fill (\ d -> (succ d, VVar (Free d))) d p in quoteC d' =<< b (constructP' p')) ps
  COp n fs k -> XApp <$> quoteC d k <*> (XOp n Nil <$> traverse (quoteV' d) fs)
  CNe v sp   -> foldl' (&) <$> quoteV' d v <*> traverse (quoteE d) sp
  CLet v b   -> XApp . XLam . pure . (PVal (PVar __),) <$> (quoteC (succ d) =<< b (VVar (Free d))) <*> quoteC d v

quoteE :: Monad m => Level -> Elim m -> m (Expr -> Expr)
quoteE d = \case
  EApp v -> flip XApp <$> quoteV' d v
  EForce -> pure XForce


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


constructP' :: Applicative m => Pattern (Value' m) -> Value' m
constructP' = \case
  PVal v -> constructV' v
  PEff e -> constructE' e

constructV' :: ValuePattern (Value' m) -> Value' m
constructV' = \case
  PWildcard -> VString' "wildcard" -- FIXME: maybe should provide a variable here anyway?
  PVar v    -> v
  PCon q fs -> VCon' q (constructV' <$> fs)

constructE' :: Applicative m => EffectPattern (Value' m) -> Value' m
constructE' (POp q fs k) = VThunk' (pure (COp q (constructV' <$> fs) (creturn k)))
