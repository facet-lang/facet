{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Eval
( -- * Evaluation
  eval
  -- * Machinery
, Eval(..)
  -- * Values
, Value(..)
, unit
  -- * Quotation
, quoteV
, E(..)
, runE
, state'
, state''
, State'(..)
, Reader'(..)
-- , Empty(..)
, toMaybe
, send'
, modify
, get''
, put''
, ask''
, reader'
) where

import Control.Algebra
import Control.Carrier.Reader
import Control.Monad (ap, guard, liftM, (>=>))
import Control.Monad.Trans.Class
import Control.Monad.Trans.Cont
import Data.Foldable
import Data.Function
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Facet.Env as Env
import Facet.Graph
import Facet.Module
import Facet.Name hiding (Op)
import Facet.Pattern
import Facet.Semialign (zipWithM)
import Facet.Snoc.NonEmpty as NE hiding ((|>))
import Facet.Syntax
import Facet.Term
import GHC.Stack (HasCallStack)
import Prelude hiding (zipWith)

eval :: (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Env (Value (Eval m)) -> Expr -> Eval m (Value (Eval m))
eval env = \case
  XVar (Global n) -> global n >>= eval env
  XVar (Free n)   -> var env n
  XLam cs         -> lam env cs
  XApp  f a       -> app env (eval env f) a
  XCon n fs       -> con n (eval env <$> fs)
  XString s       -> string s
  XDict os        -> VDict <$> traverse (traverse (eval env)) os
  XLet p v b      -> eval env v >>= \ v' -> eval (env |> fromMaybe (error "eval: non-exhaustive pattern in let") (matchV id p v')) b
  XComp p b       -> lam env [(PDict p, b)] -- FIXME: this won’t roundtrip correctly

global :: Has (Reader Graph :+: Reader Module) sig m => RName -> Eval m Expr
global n = do
  mod <- lift ask
  graph <- lift ask
  case lookupQ graph mod (toQ n) of
    [_ :=: DTerm (Just v) _] -> pure v -- FIXME: store values in the module graph
    _                        -> error "throw a real error here"

var :: (HasCallStack, Applicative m) => Env (Value m) -> LName Index -> m (Value m)
var env n = pure (index env n)

lam :: Env (Value (Eval m)) -> [(Pattern Name, Expr)] -> Eval m (Value (Eval m))
lam env cs = pure $ VLam env cs

app :: (HasCallStack, Has (Reader Graph :+: Reader Module) sig m, MonadFail m) => Env (Value (Eval m)) -> Eval m (Value (Eval m)) -> Expr -> Eval m (Value (Eval m))
app envCallSite f a = f >>= \case
  VLam env cs -> k a where
    k = foldl' (\ vs (p, b) -> eval envCallSite >=> fromMaybe (vs a) . matchV (\ vs -> eval (env |> vs) b) p) (const (fail "non-exhaustive patterns in lambda")) cs
  VCont k     -> k =<< eval envCallSite a
  _           -> fail "expected lambda/continuation"

string :: Text -> Eval m (Value (Eval m))
string = pure . VString

con :: RName -> [Eval m (Value (Eval m))] -> Eval m (Value (Eval m))
con n fs = VCon n <$> sequenceA fs


-- Machinery

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
  = VVar (Var (LName Level))
  -- | Value; data constructors.
  | VCon RName [Value m]
  -- | Value; strings.
  | VString Text
  -- | Computation; lambdas.
  | VLam (Env (Value m)) [(Pattern Name, Expr)]
  -- | Computation; continuations, used in effect handlers.
  | VCont (Value m -> m (Value m))
  | VDict [RName :=: Value m]

unit :: Value m
unit = VCon (NE.FromList ["Data", "Unit"] :.: U "unit") []


-- Elimination

matchV :: (Pattern (Name :=: Value m) -> a) -> Pattern Name -> Value m -> Maybe a
matchV k p s = case p of
  PWildcard -> pure (k PWildcard)
  PVar n    -> pure (k (PVar (n :=: s)))
  PCon n ps
    | VCon n' fs <- s -> k . PCon n' <$ guard (n == n') <*> zipWithM (matchV id) ps fs
  PCon{}    -> Nothing
  PDict ps
    | VDict os <- s -> k . PDict <$> zipWithM (\ (n1 :=: p) (n2 :=: o) -> (n1 :=: (p :=: o)) <$ guard (n1 == n2)) ps os
  PDict{}   -> Nothing


-- Quotation

quoteV :: Monad m => Level -> Value m -> m Expr
quoteV d = \case
  VLam _ cs -> pure $ XLam cs
  VCont k   -> quoteV (succ d) =<< k (VVar (Free (LName d __)))
  VVar v    -> pure (XVar (fmap (levelToIndex d) <$> v))
  VCon n fs -> XCon n <$> traverse (quoteV d) fs
  VString s -> pure $ XString s
  VDict os  -> XDict <$> traverse (traverse (quoteV d)) os


newtype E sig r i a = E (sig (E sig r i) i r -> Cont r a)
  deriving (Functor)

instance Functor (sig (E sig r i) i) => Applicative (E sig r i) where
  pure a = E $ \ _ -> pure a
  (<*>) = ap

instance Functor (sig (E sig r i) i) => Monad (E sig r i) where
  E run >>= f = E $ \ d -> run d >>= runE d . f

runE :: sig (E sig r i) i r -> E sig r i a -> Cont r a
runE d (E run) = run d


newtype Empty m a b = Empty { empty :: forall e . (e -> m a) -> m b }
  deriving (Functor)

toMaybe :: E Empty (Maybe a) a a -> Maybe a
toMaybe = (`runCont` Just) . runE Empty{ empty = \ _k -> pure Nothing }


data Reader' r m a b = Reader'
  { ask'   :: (r -> m a) -> m b
  , local' :: forall x . (r -> r) -> m x -> (x -> m a) -> m b }
  deriving (Functor)

ask'' :: E (Reader' r) b i r
ask'' = E $ \ d@Reader'{ ask' } -> runE d (send' ask')

reader' :: r -> E (Reader' r) a a a -> Cont b a
reader' = fmap reset . runE . dict
  where
  reader' :: r -> E (Reader' r) a a a -> E (Reader' r) b a a
  reader' r m = E $ \ _ -> reset $ cont $ \ k -> runCont (runE (dict r) m) k
  dict :: r -> Reader' r (E (Reader' r) a a) a a
  dict r = Reader'
    { ask'   = \     k -> reader' r (k r)
    -- , local' = \ f m k -> reader' r (k =<< reader' (f r) m)
    }


data State' s m a b = State'
  { get' :: (s -> m a) -> m b
  , put' :: s -> (() -> m a) -> m b }
  deriving (Functor)

send' :: ((c -> E sig b i i) -> E sig b i b) -> E sig b i c
send' hdl = E $ \ d -> cont $ \ k -> evalCont (runE d (hdl (E . const . cont . const . k)))

state'' :: s -> E (State' s) (s, a) a a -> Cont x (s, a)
state'' = state' (,)

state' :: (s -> a -> b) -> s -> E (State' s) b a a -> Cont x b
state' z s m = reset $ cont $ \ k -> runCont (runE (dict z s) m) (k . z s)
  where
  state' :: (s -> a -> b) -> s -> E (State' s) b a a -> E (State' s) b a b
  state' z s m = E $ \ _ -> reset $ cont $ \ k -> runCont (runE (dict z s) m) (k . z s)
  dict :: (s -> a -> b) -> s -> State' s (E (State' s) b a) a b
  dict z s = State'
    { get' = \   k -> state' z s (k s)
    , put' = \ s k -> state' z s (k ()) }

modify :: (s -> s) -> E (State' s) r i ()
modify f = put'' . f =<< get''

get'' :: E (State' s) r i s
get'' = E $ \ d@State'{ get' } -> runE d (send' get')

put'' :: s -> E (State' s) r i ()
put'' s = E $ \ d@State'{ put' } -> runE d (send' (put' s))
