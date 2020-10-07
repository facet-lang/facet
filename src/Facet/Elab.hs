{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Elab
( Context
, implicit
, elab
, Elab(..)
, Check(..)
, Synth(..)
, check
, unify
  -- * General
, global
  -- * Types
, elabType
, _Type
, _Unit
, (.$)
, (.*)
, (-->)
, (>~>)
  -- * Expressions
, elabExpr
, ($$)
, tlam
, lam
, unit
, (**)
  -- * Declarations
, elabDecl
  -- * Modules
, elabModule
) where

import           Control.Algebra
import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Effect.Parser.Span (Span(..))
import           Control.Lens (Prism', preview, review)
import           Data.Bifunctor (first)
import           Data.Foldable (toList)
import qualified Data.IntMap as IntMap
import           Data.Semigroup (stimes)
import qualified Data.Text as T
import           Facet.Carrier.Error.Context
import qualified Facet.Core as C
import qualified Facet.Core.Expr as CE
import qualified Facet.Core.Module as CM
import qualified Facet.Core.Pattern as CP
import           Facet.Core.Type as CT
import qualified Facet.Env as Env
import           Facet.Name (E, MName(..), Name(..), QName(..), T)
import qualified Facet.Name as N
import           Facet.Pretty (reflow)
import qualified Facet.Print as P
import           Facet.Stack
import qualified Facet.Surface.Comp as SC
import qualified Facet.Surface.Decl as SD
import qualified Facet.Surface.Expr as SE
import qualified Facet.Surface.Module as SM
import qualified Facet.Surface.Pattern as SP
import qualified Facet.Surface.Type as ST
import           Facet.Syntax
import           Prelude hiding ((**))
import           Silkscreen (Pretty, colon, fillSep, flatAlt, group, line, nest, pretty, softline, space, (</>))

type Context = IntMap.IntMap Type

implicit :: Env.Env
implicit = Env.fromList [ (N.T (N.TName (T.pack "Type")), MName (T.pack "Facet") ::: C._Type) ]

elab :: Applicative m => Span -> Env.Env -> Context -> Elab m a -> m (Either (Span, P.Print) a)
elab s e c (Elab m) = runError (curry (pure . Left)) (pure . Right) s (m e c)

newtype Elab m a = Elab (Env.Env -> Context -> ErrorC Span P.Print m a)
  deriving (Algebra (Reader Env.Env :+: Reader Context :+: Error P.Print :+: Reader Span :+: sig), Applicative, Functor, Monad) via ReaderC Env.Env (ReaderC Context (ErrorC Span P.Print m))


newtype Check m a = Check { runCheck :: Type -> m a }
  deriving (Algebra (Reader Type :+: sig), Applicative, Functor, Monad) via ReaderC Type m

newtype Synth m a = Synth { synth :: m (a ::: Type) }

instance Functor m => Functor (Synth m) where
  fmap f (Synth m) = Synth (first f <$> m)

check :: (Check m a ::: Type) -> m a
check = uncurryAnn runCheck


unify
  :: Has (Throw P.Print) sig m
  => Type
  -> Type
  -> m ()
unify t1 t2 = go t1 t2
  where
  go t1 t2 = case (out t1, out t2) of
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
    _                       -> couldNotUnify t1 t2
  goS Nil        Nil        = Just (pure ())
  goS (i1 :> l1) (i2 :> l2) = (*>) <$> goS i1 i2 <*> Just (go l1 l2)
  goS _          _          = Nothing


-- General

global
  :: (Has (Reader Env.Env :+: Throw P.Print) sig m)
  => N.DName
  -> Synth m QName
global n = Synth $ asks (Env.lookup n) >>= \case
  Just b  -> pure (tm b :.: n ::: ty b)
  Nothing -> freeVariable (pretty n)

bound
  :: (Has (Reader Context :+: Throw P.Print) sig m, Pretty (Name a))
  => Name a
  -> Synth m (Name a)
bound n = Synth $ asks (IntMap.lookup (id' n)) >>= \case
  Just b  -> pure (n ::: b)
  Nothing -> freeVariable (pretty n)

app
  :: Has (Throw P.Print) sig m
  => (a -> a -> a)
  -> Synth m a
  -> Check m a
  -> Synth m a
app ($$) f a = Synth $ do
  f' ::: _F <- synth f
  (_A, _B) <- expectFunctionType (pretty "in application") _F
  a' <- check (a ::: _A)
  pure $ f' $$ a' ::: _B


-- Types

elabType
  :: Has (Reader Context :+: Reader Env.Env :+: Reader Span :+: Throw P.Print) sig m
  => (ST.Type ::: Maybe Type)
  -> m (Type ::: Type)
elabType (t ::: _K) = ST.fold alg t _K
  where
  alg = \case
    ST.Free  n -> switch $ synth (C.tglobal <$> global n)
    ST.Bound n -> switch $ synth (C.tbound <$> bound n)
    ST.Hole  n -> \ _K -> hole (n ::: _K)
    ST.Type    -> switch $ synth _Type
    ST.Void    -> switch $ synth _Void
    ST.Unit    -> switch $ synth _Unit
    t ST.:=> b -> switch $ synth (fmap _check t >~> _check b)
    f ST.:$  a -> switch $ synth (_synth f .$  _check a)
    a ST.:-> b -> switch $ synth (_check a --> _check b)
    l ST.:*  r -> switch $ synth (_check l .*  _check r)
    ST.Loc s b -> local (const s) . b
    where
    _check r = tm <$> Check (r . Just)
    _synth r = Synth (r Nothing)
    switch m = \case
      Just _K -> m >>= \ r -> r <$ unify (ty r) _K
      _       -> m


_Type :: (Applicative m, C.Type t) => Synth m t
_Type = Synth $ pure $ C._Type ::: C._Type

_Void :: (Applicative m, C.Type t) => Synth m t
_Void = Synth $ pure $ C._Void ::: C._Type

_Unit :: (Applicative m, C.Type t) => Synth m t
_Unit = Synth $ pure $ C._Unit ::: C._Type

(.$)
  :: (Has (Throw P.Print) sig m, C.Type t)
  => Synth m t
  -> Check m t
  -> Synth m t
(.$) = app (C..$)

infixl 9 .$

(.*)
  :: (Applicative m, C.Type t)
  => Check m t
  -> Check m t
  -> Synth m t
a .* b = Synth $ do
  a' <- check (a ::: C._Type)
  b' <- check (b ::: C._Type)
  pure $ a' C..* b' ::: C._Type

infixl 7 .*

(-->)
  :: (Applicative m, C.Type t)
  => Check m t
  -> Check m t
  -> Synth m t
a --> b = Synth $ do
  a' <- check (a ::: C._Type)
  b' <- check (b ::: C._Type)
  pure $ (a' C.--> b') ::: C._Type

infixr 2 -->

(>~>)
  :: Has (Reader Context) sig m
  => (Name T ::: Check m Type)
  -> Check m Type
  -> Synth m Type
(n ::: t) >~> b = Synth $ do
  _T <- check (t ::: C._Type)
  ftb' <- n ::: _T |- ((n ::: _T) C.>=>) <$> check (b ::: C._Type)
  pure $ ftb' ::: C._Type

infixr 1 >~>


-- Expressions

elabExpr
  :: Has (Reader Context :+: Reader Env.Env :+: Reader Span :+: Throw P.Print) sig m
  => (SE.Expr ::: Maybe Type)
  -> m (CE.Expr ::: Type)
elabExpr (t ::: _T) = SE.fold alg t _T
  where
  alg = \case
    SE.Free  n -> switch $ synth (C.global <$> global n)
    SE.Bound n -> switch $ synth (C.bound <$> bound n)
    SE.Hole  n -> \ _T -> hole (n ::: _T)
    f SE.:$  a -> switch $ synth (_synth f $$  _check a)
    l SE.:*  r -> check (_check l **  _check r) (pretty "product")
    SE.Unit    -> switch $ synth unit
    SE.Comp cs -> check (comp (map (fmap _check) cs)) (pretty "computation")
    SE.Loc s b -> local (const s) . b
    where
    _check r = tm <$> Check (r . Just)
    _synth r = Synth (r Nothing)
    check m msg _T = expectChecked _T msg >>= \ _T -> (::: _T) <$> runCheck m _T
    switch m = \case
      Just _T -> m >>= \ r -> r <$ unify (ty r) _T
      _       -> m


($$)
  :: (Has (Throw P.Print) sig m, C.Expr expr)
  => Synth m expr
  -> Check m expr
  -> Synth m expr
($$) = app (C.$$)

tlam
  :: (Has (Reader Context :+: Throw P.Print) sig m, C.Expr expr)
  => Name T
  -> Check m expr
  -> Check m expr
tlam n b = Check $ \ ty -> do
  (_T, _B) <- expectQuantifiedType (reflow "when checking type lambda") ty
  _T |- C.tlam n <$> check (b ::: _B)

lam
  :: (Has (Reader Context :+: Throw P.Print) sig m, C.Expr expr)
  => Name E
  -> Check m expr
  -> Check m expr
lam n b = Check $ \ _T -> do
  (_A, _B) <- expectFunctionType (reflow "when checking lambda") _T
  n ::: _A |- C.lam (review CP.var_ n) <$> check (b ::: _B)

unit :: (Applicative m, C.Expr t) => Synth m t
unit = Synth . pure $ C.unit ::: C._Unit

(**)
  :: (Has (Throw P.Print) sig m, C.Expr expr)
  => Check m expr
  -> Check m expr
  -> Check m expr
l ** r = Check $ \ _T -> do
  (_L, _R) <- expectProductType (reflow "when checking product") _T
  l' <- check (l ::: _L)
  r' <- check (r ::: _R)
  pure (l' C.** r')

comp
  :: (Has (Reader Context :+: Reader Span :+: Throw P.Print) sig m, C.Expr expr)
  => [SC.Clause (Check m expr)]
  -> Check m expr
comp cs = do
  cs' <- traverse clause cs
  -- FIXME: extend Core to include pattern matching so this isn’t broken
  -- FIXME: extend Core to include computation types
  pure $ head cs'

clause
  :: (Has (Reader Context :+: Reader Span :+: Throw P.Print) sig m, C.Expr expr)
  => SC.Clause (Check m expr)
  -> Check m expr
clause = SC.fold $ \case
  SC.Clause p b -> Check $ \ _T -> do
    (_A, _B) <- expectFunctionType (reflow "when checking clause") _T
    p' <- check (pattern p ::: _A)
    foldr (|-) (C.lam (tm <$> p') <$> check (b ::: _B)) p'
  SC.Body e   -> e
  SC.Loc s c  -> local (const s) c


pattern
  :: Has (Reader Span :+: Throw P.Print) sig m
  => SP.Pattern (Name E)
  -> Check m (CP.Pattern (Name E ::: Type))
pattern = SP.fold $ \ s -> local (const s) . \case
  SP.Wildcard -> pure (review CP.wildcard_ ())
  SP.Var n    -> Check $ \ _T -> pure (review CP.var_ (n ::: _T))
  SP.Tuple ps -> Check $ \ _T -> review CP.tuple_ . toList <$> go _T (fromList ps)
    where
    go _T = \case
      Nil      -> Nil      <$  unify C._Unit _T
      Nil :> p -> (Nil :>) <$> check (p ::: _T)
      ps  :> p -> do
        (_L, _R) <- expectProductType (reflow "when checking tuple pattern") _T
        (:>) <$> go _L ps <*> check (p ::: _R)


-- Declarations

elabDecl
  :: Has (Reader Context :+: Reader Env.Env :+: Reader Span :+: Throw P.Print) sig m
  => SD.Decl
  -> m (Check m CE.Expr ::: Type)
elabDecl = SD.fold alg
  where
  alg s = local (const s) . \case
    (n ::: t) SD.:=> b -> do
      _T ::: _  <- elabType (t ::: Just C._Type)
      b' ::: _B <- n ::: _T |- b
      pure $ tlam n b' ::: ((n ::: _T) C.>=> _B)

    (n ::: t) SD.:-> b -> do
      _T ::: _  <- elabType (t ::: Just C._Type)
      b' ::: _B <- n ::: _T |- b
      pure $ lam n b' ::: (_T C.--> _B)

    t SD.:= b -> do
      _T ::: _ <- elabType (t ::: Just C._Type)
      pure $ _check (elabExpr . (b :::)) ::: _T

  _check r = tm <$> Check (r . Just)


-- Modules

elabModule
  :: Has (Reader Context :+: Reader Env.Env :+: Reader Span :+: Throw P.Print) sig m
  => SM.Module
  -> m CM.Module
-- FIXME: elaborate all the types first, and only then the terms
elabModule (SM.Module s n ds) = local (const s) $ evalState (mempty @Env.Env) $ C.module' n <$> traverse (elabDef n) ds

elabDef
  :: Has (Reader Context :+: Reader Span :+: State Env.Env :+: Throw P.Print) sig m
  => MName
  -> SM.Def
  -> m (QName, C.Def CE.Expr Type ::: Type)
elabDef mname (SM.Def s n d) = local (const s) $ do
  env <- get @Env.Env
  e' ::: _T <- runReader env $ do
    e ::: _T <- elabDecl d
    e' <- check (e ::: _T)
    pure $ e' ::: _T

  modify $ Env.insert (mname :.: n ::: _T)
  -- FIXME: extend the module
  -- FIXME: support defining types
  pure (mname :.: n, C.DTerm e' ::: interpret _T)


-- Context

(|-) :: Has (Reader Context) sig m => Name b ::: Type -> m a -> m a
n ::: t |- m = local (IntMap.insert (id' n) t) m

infix 1 |-


-- Failures

err :: Has (Throw P.Print) sig m => P.Print -> m a
err = throwError . group

hole :: Has (Throw P.Print) sig m => (T.Text ::: Maybe Type) -> m (a ::: Type)
hole (n ::: t) = case t of
  Just t  -> err $ fillSep [pretty "found", pretty "hole", pretty n, colon, interpret t]
  Nothing -> couldNotSynthesize (fillSep [ pretty "hole", pretty n ])

mismatch :: Has (Throw P.Print) sig m => P.Print -> P.Print -> P.Print -> m a
mismatch msg exp act = err $ msg
  </> pretty "expected:" <> print exp
  </> pretty "  actual:" <> print act
  where
  -- line things up nicely for e.g. wrapped function types
  print = nest 2 . (flatAlt (line <> stimes (3 :: Int) space) mempty <>)

couldNotUnify :: Has (Throw P.Print) sig m => Type -> Type -> m a
couldNotUnify t1 t2 = mismatch (reflow "could not unify") (interpret t2) (interpret t1)

couldNotSynthesize :: Has (Throw P.Print) sig m => P.Print -> m a
couldNotSynthesize msg = err $ reflow "could not synthesize a type for" <> softline <> msg

freeVariable :: Has (Throw P.Print) sig m => P.Print -> m a
freeVariable v = err $ fillSep [reflow "variable not in scope:", v]

expectChecked :: Has (Throw P.Print) sig m => Maybe Type -> P.Print -> m Type
expectChecked t msg = maybe (couldNotSynthesize msg) pure t


-- Patterns

expectMatch :: Has (Throw P.Print) sig m => Prism' Type out -> P.Print -> P.Print -> Type -> m out
expectMatch pat exp s _T = maybe (mismatch s exp (interpret _T)) pure (preview pat _T)

expectQuantifiedType :: Has (Throw P.Print) sig m => P.Print -> Type -> m (Name T ::: Type, Type)
expectQuantifiedType = expectMatch forAll_ (pretty "{_} -> _")

expectFunctionType :: Has (Throw P.Print) sig m => P.Print -> Type -> m (Type, Type)
expectFunctionType = expectMatch arrow_ (pretty "_ -> _")

expectProductType :: Has (Throw P.Print) sig m => P.Print -> Type -> m (Type, Type)
expectProductType = expectMatch prd_ (pretty "(_, _)")
