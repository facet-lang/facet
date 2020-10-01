{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Elab
( Env
, Context
, implicit
, elab
, Elab(..)
, Check(..)
, Synth(..)
, check
, switch
, unify
  -- * General
, global
  -- * Types
, _Type
, _Unit
, (.$)
, (.*)
, (-->)
, (>~>)
  -- * Expressions
, ($$)
, tlam
, lam0
) where

import           Control.Algebra
import           Control.Carrier.Reader
import           Control.Effect.Error
import           Control.Effect.Parser.Span (Span(..))
import           Data.Bifunctor (first)
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import qualified Data.Text as T
import qualified Facet.Core as C
import           Facet.Name (Name(..), prettyNameWith)
import qualified Facet.Print as P
import qualified Facet.Surface as S
import           Facet.Syntax
import           Facet.Type
import           Silkscreen (fillSep, group, pretty, (<+>), (</>))

type Env = Map.Map T.Text Type
type Context = IntMap.IntMap Type

implicit :: Env
implicit = Map.fromList [ (T.pack "Type", C._Type) ]

elab :: (Elab m a ::: Maybe Type) -> m a
elab = runEnv implicit mempty . uncurryAnn runElab

runEnv :: Env -> Context -> EnvC m a -> m a
runEnv e c m = runEnvC m e c

newtype EnvC m a = EnvC { runEnvC :: Env -> Context -> m a }
  deriving (Algebra (Reader Env :+: Reader Context :+: sig), Applicative, Functor, Monad) via ReaderC Env (ReaderC Context m)

newtype Elab m a = Elab { runElab :: Maybe Type -> EnvC m a }
  deriving (Algebra (Reader (Maybe Type) :+: Reader Env :+: Reader Context :+: sig), Applicative, Functor, Monad) via ReaderC (Maybe Type) (EnvC m)

fromCheck :: Has (Error P.Print) sig m => Check m a -> Elab m (a ::: Type)
fromCheck m = Elab $ \case
  Just t  -> (::: t) <$> check (m ::: t)
  Nothing -> couldNotSynthesize

toCheck :: Has (Error P.Print) sig m => Elab m (a ::: Type) -> Check m a
toCheck m = Check $ \ _T -> do
  a ::: _T' <- runElab m (Just _T)
  a <$ unify _T _T'

fromSynth :: Has (Error P.Print) sig m => Synth m a -> Elab m (a ::: Type)
fromSynth (Synth m) = Elab $ \case
  Just _T -> do
    a ::: _T' <- m
    (a ::: _T') <$ unify _T _T'
  Nothing -> m

toSynth :: Elab m (a ::: Type) -> Synth m a
toSynth (Elab m) = Synth (m Nothing)

instance Has (Reader Span) sig m => S.Located (Elab m a) where
  locate = local . const

instance Has (Error P.Print) sig m => S.Type (Elab m (Type ::: Type)) where
  tglobal = fmap (first C.tglobal) . fromSynth . global . S.getTName
  tbound n = first C.tbound <$> fromSynth (localVar n P.tvar)
  (n ::: t) >~> b = fromSynth $ (n ::: toCheck t) >~> toCheck b
  a --> b = fromSynth $ toCheck a --> toCheck b
  f .$  a = fromSynth $ toSynth f .$  toCheck a
  l .*  r = fromSynth $ toCheck l .*  toCheck r

  _Unit = fromSynth _Unit
  _Type = fromSynth _Type

instance (C.Expr expr, Has (Error P.Print) sig m) => S.Expr (Elab m (expr ::: Type)) where
  global = fmap (first C.global) . fromSynth . global . S.getEName
  bound n = first C.bound <$> fromSynth (localVar n P.evar)
  lam0 n b = fromCheck $ lam0 n (toCheck b)
  lam _ _ = tbd
  f $$ a = fromSynth $ toSynth f $$ toCheck a
  unit = tbd
  _ ** _ = tbd

-- FIXME: this should probably elaborate to nested elaborators, one at type level, producing one at expression level
instance (C.Expr expr, Has (Error P.Print) sig m) => S.Decl (Elab m (expr ::: Type)) (Elab m (Type ::: Type)) (Elab m (expr ::: Type)) where
  t .= b = Elab $ \ _T -> do -- FIXME: what are we supposed to do with _T? what’s the type of a declaration anyway?
    _T' ::: _ <- runElab t (Just C._Type)
    b' ::: _ <- runElab b (Just _T')
    pure $ b' ::: _T'

  (n ::: t) >=> b = Elab $ \ _T -> do
    _T ::: _ <- runElab t (Just C._Type)
    b' ::: _B <- n ::: _T |- runElab b Nothing
    pure $ C.tlam n b' ::: ((n ::: _T) C.==> _B)

  (n ::: t) >-> b = Elab $ \ _T -> do
    _T ::: _ <- runElab t (Just C._Type)
    b' ::: _B <- n ::: _T |- runElab b Nothing
    pure $ C.lam0 n b' ::: (_T C.--> _B)

instance (C.Expr expr, C.Type ty, C.Module expr ty mod, Has (Error P.Print) sig m) => S.Module (Elab m (expr ::: Type)) (Elab m (Type ::: Type)) (Elab m (expr ::: Type)) (Elab m mod) where
  n .:. d = do
    e ::: _T <- d -- FIXME: check _T at Type, check e at _T -- d should probably be two separate elaborators
    pure $ S.getDName n C..:. interpret _T := e


newtype Check m a = Check { runCheck :: Type -> EnvC m a }
  deriving (Algebra (Reader Type :+: Reader Env :+: Reader Context :+: sig), Applicative, Functor, Monad) via ReaderC Type (EnvC m)

newtype Synth m a = Synth { runSynth :: EnvC m (a ::: Type) }

instance Functor m => Functor (Synth m) where
  fmap f (Synth m) = Synth (first f <$> m)

check :: (Check m a ::: Type) -> EnvC m a
check = uncurryAnn runCheck

switch :: Has (Error P.Print) sig m => Synth m a -> Check m a
switch s = Check $ \ _T -> do
  a ::: _T' <- runSynth s
  a <$ unify _T _T'

unify :: Has (Error P.Print) sig m => Type -> Type -> m ()
unify t1 t2 = go t1 t2
  where
  go = curry $ \case
    (Type,      Type)       -> pure ()
    (Unit,      Unit)       -> pure ()
    (l1 :* r1,  l2 :* r2)   -> go l1 l2 *> go r1 r2
    -- FIXME: we try to unify Type-the-global with Type-the-constant
    -- FIXME: resolve globals to try to progress past certain inequalities
    (f1 :$ a1,  f2 :$ a2)
      | f1 == f2
      , Just _ <- goS a1 a2 -> pure ()
    (a1 :-> b1, a2 :-> b2)  -> go a1 a2 *> go b1 b2
    (t1 :=> b1, t2 :=> b2)  -> go (ty t1) (ty t2) *> go b1 b2
    -- FIXME: build and display a diff of the root types
    (t1, t2) -> couldNotUnify t1 t2
  goS Nil        Nil        = Just (pure ())
  goS (i1 :> l1) (i2 :> l2) = (*>) <$> goS i1 i2 <*> Just (go l1 l2)
  goS _          _          = Nothing


-- General

global :: Has (Error P.Print) sig m => T.Text -> Synth m T.Text
global s = Synth $ asks (Map.lookup s) >>= \case
  Just b  -> pure (s ::: b)
  Nothing -> freeVariable (pretty s)

localVar :: Has (Error P.Print) sig m => Name -> (Int -> P.Print) -> Synth m Name
localVar n var = Synth $ asks (IntMap.lookup (id' n)) >>= \case
  Just b  -> pure (n ::: b)
  Nothing -> freeVariable (prettyNameWith var n)

app :: Has (Error P.Print) sig m => (a -> a -> a) -> Synth m a -> Check m a -> Synth m a
app ($$) f a = Synth $ do
  f' ::: _F <- runSynth f
  (_A, _B) <- expectFunctionType (pretty "in application") _F
  a' <- check (a ::: _A)
  pure $ f' $$ a' ::: _B


-- Types

_Type :: (Applicative m, C.Type t) => Synth m t
_Type = Synth $ pure $ C._Type ::: C._Type

_Unit :: (Applicative m, C.Type t) => Synth m t
_Unit = Synth $ pure $ C._Unit ::: C._Type

(.$) :: (Has (Error P.Print) sig m, C.Type t) => Synth m t -> Check m t -> Synth m t
(.$) = app (C..$)

infixl 9 .$

(.*) :: (Monad m, C.Type t) => Check m t -> Check m t -> Synth m t
a .* b = Synth $ do
  a' <- check (a ::: C._Type)
  b' <- check (b ::: C._Type)
  pure $ a' C..* b' ::: C._Type

infixl 7 .*

(-->) :: (Monad m, C.Type t) => Check m t -> Check m t -> Synth m t
a --> b = Synth $ do
  a' <- check (a ::: C._Type)
  b' <- check (b ::: C._Type)
  pure $ (a' C.--> b') ::: C._Type

infixr 2 -->

(>~>)
  :: Algebra sig m
  => (Name ::: Check m Type)
  -> Check m Type
  -> Synth m Type
(n ::: t) >~> b = Synth $ do
  _T <- check (t ::: C._Type)
  ftb' <- n ::: _T |- ((n ::: _T) C.==>) <$> check (b ::: C._Type)
  pure $ ftb' ::: C._Type

infixr 1 >~>


-- Expressions

($$) :: (C.Expr expr, Has (Error P.Print) sig m) => Synth m expr -> Check m expr -> Synth m expr
($$) = app (C.$$)

tlam :: (C.Expr expr, Has (Error P.Print) sig m) => Name -> Check m expr -> Check m expr
tlam n b = Check $ \ ty -> do
  (n', _T, _B) <- expectQuantifiedType (fromWords "when checking type lambda") ty
  n' ::: _T |- C.tlam n <$> check (b ::: _B)

lam0 :: (C.Expr expr, Has (Error P.Print) sig m) => Name -> Check m expr -> Check m expr
lam0 n b = Check $ \ ty -> do
  (_A, _B) <- expectFunctionType (fromWords "when checking lambda") ty
  n ::: _A |- C.lam0 n <$> check (b ::: _B)


-- Context

(|-) :: Has (Reader Context) sig m => Name ::: Type -> m a -> m a
n ::: t |- m = local (IntMap.insert (id' n) t) m

infix 1 |-


-- Failures

fromWords :: String -> P.Print
fromWords = fillSep . map pretty . words

err :: Has (Error P.Print) sig m => P.Print -> m a
err = throwError . group

tbd :: Has (Error P.Print) sig m => m a
tbd = err $ pretty "TBD"

mismatch :: Has (Error P.Print) sig m => P.Print -> P.Print -> P.Print -> m a
mismatch msg exp act = err $ msg
  </> pretty "expected:" <+> exp
  </> pretty "  actual:" <+> act

couldNotUnify :: Has (Error P.Print) sig m => Type -> Type -> m a
couldNotUnify t1 t2 = mismatch (fromWords "could not unify") (interpret t2) (interpret t1)

couldNotSynthesize :: Has (Error P.Print) sig m => m a
couldNotSynthesize = err $ fromWords "could not synthesize a type"

freeVariable :: Has (Error P.Print) sig m => P.Print -> m a
freeVariable v = err $ fromWords "variable not in scope:" <+> v


-- Patterns

expectQuantifiedType :: Has (Error P.Print) sig m => P.Print -> Type -> m (Name, Type, Type)
expectQuantifiedType s = \case
  (n ::: _T) :=> _B -> pure (n, _T, _B)
  _T                -> mismatch s (pretty "{_} -> _") (interpret _T)

expectFunctionType :: Has (Error P.Print) sig m => P.Print -> Type -> m (Type, Type)
expectFunctionType s = \case
  _A :-> _B -> pure (_A, _B)
  _T        -> mismatch s (pretty "_ -> _") (interpret _T)
