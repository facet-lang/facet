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
, state'
, state''
, E(..)
, runE
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
import Control.Monad (ap, guard, liftM, (<=<), (>=>))
import Control.Monad.Trans.Class
import Control.Monad.Trans.Cont
import Data.Foldable
import Data.Function
import Data.Maybe (fromMaybe)
import Data.Profunctor
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


class (Profunctor p, Monad m) => LeftPromodule m p | p -> m where
  bindl :: (a -> (b `p` c)) -> m a -> (b `p` c)
  bindl f m = joinl (fmap f m)

  joinl :: m (a `p` b) -> (a `p` b)
  joinl = bindl id

  {-# MINIMAL bindl | joinl #-}

class (Profunctor p, Monad m) => RightPromodule m p | p -> m where
  dibind :: (a' -> m a) -> (b -> m b') -> (a `p` b) -> (a' `p` b')
  dibind f g = lbind f . rbind g

  lbind :: (a' -> m a) -> (a `p` b) -> (a' `p` b)
  lbind = (`dibind` return)

  rbind :: (b -> m b') -> (a `p` b) -> (a `p` b')
  rbind = (return `dibind`)

  {-# MINIMAL dibind | (lbind, rbind) #-}


newtype E sig r a = E (sig (E sig r) a r -> Cont r a)

instance Profunctor (sig (E sig r)) => Functor (E sig r) where
  fmap f (E run) = E $ \ d -> f <$> run (lmap f d)

instance RightPromodule (E sig r) (sig (E sig r)) => Applicative (E sig r) where
  pure a = E $ \ _ -> pure a
  (<*>) = ap

instance RightPromodule (E sig r) (sig (E sig r)) => Monad (E sig r) where
  E run >>= f = E $ \ d -> run (lbind f d) >>= runE d . f

runE :: sig (E sig r) a r -> E sig r a -> Cont r a
runE d (E run) = run d

liftE :: Cont r a -> E sig r a
liftE = E . const


newtype Empty m a b = Empty { empty :: forall e . (e -> m a) -> m b }
  deriving (Functor)

instance Functor m => Profunctor (Empty m) where
  dimap f g Empty{ empty } = Empty{ empty = \ k -> g <$> empty (fmap f . k) }

instance Monad m => RightPromodule m (Empty m) where
  dibind f g Empty{ empty } = Empty{ empty = \ k -> g =<< empty (f <=< k) }

toMaybe :: E Empty (Maybe a) a -> Maybe a
toMaybe = (`runCont` Just) . runE Empty{ empty = \ _k -> pure Nothing }


data Reader' r m a b = Reader' { ask' :: (r -> m a) -> m b, local' :: forall x . (r -> r) -> m x -> (x -> m a) -> m b }
  deriving (Functor)

instance Functor m => Profunctor (Reader' r m) where
  dimap f g Reader'{ ask', local' } = Reader'{ ask' = \ k -> g <$> ask' (fmap f . k), local' = \ h m k -> g <$> local' h m (fmap f . k) }

instance Monad m => RightPromodule m (Reader' r m) where
  dibind f g Reader'{ ask', local' } = Reader'{ ask' = \ k -> g =<< ask' (f <=< k), local' = \ h m k -> g =<< local' h m (f <=< k) }


ask'' :: E (Reader' r) x r
ask'' = E $ \ d@Reader'{ ask' } -> runE d (send' ask')

reader' :: r -> E (Reader' r) a a -> E (Reader' r) x a
reader' r m = E $ \ _ -> reset $ runE dict m
  where
  dict = Reader'
    { ask'   = \     k -> reader' r (k r)
    -- , local' = \ f m k -> reader' r (k =<< reader' (f r) m)
    }


data State' s m a b = State' { get' :: (s -> m a) -> m b, put' :: s -> (() -> m a) -> m b }
  deriving (Functor)

instance Functor m => Profunctor (State' r m) where
  dimap f g State'{ get', put' } = State'{ get' = \ k -> g <$> get' (fmap f . k), put' = \ s k -> g <$> put' s (fmap f . k) }

instance Monad m => RightPromodule m (State' r m) where
  dibind f g State'{ get', put' } = State'{ get' = \ k -> g =<< get' (f <=< k), put' = \ s k -> g =<< put' s (f <=< k) }


send' :: RightPromodule (E sig r) (sig (E sig r)) => ((c -> E sig r c) -> E sig r r) -> E sig r c
send' hdl = E $ \ d -> cont $ \ k -> evalCont (runE (lbind (liftE . cont . const) d) (hdl (liftE . cont . const . k)))

state'' :: s -> E (State' s) (s, a) a -> Cont x (s, a)
state'' = state' (,)

state' :: forall s a b x . (s -> a -> b) -> s -> E (State' s) b a -> Cont x b
state' z s m = reset $ ContT $ \ k -> runContT (runE (dict s) m) (k . z s)
  where
  state' :: (s -> a -> b) -> s -> E (State' s) b a -> E (State' s) y b
  state' z s m = E $ \ d -> reset $ ContT $ \ k -> runContT (runE (dict s) m) (k . z s)
  dict s = State'
    { get' = \   k -> state' z s (k s)
    , put' = \ s k -> state' z s (k ()) }

modify :: (s -> s) -> E (State' s) x ()
modify f = put'' . f =<< get''

get'' :: E (State' s) x s
get'' = E $ \ d@State'{ get' } -> runE d (send' get')

put'' :: s -> E (State' s) x ()
put'' s = E $ \ d@State'{ put' } -> runE d (send' (put' s))
