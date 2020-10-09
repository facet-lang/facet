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
import           Control.Category ((>>>))
import           Control.Effect.Parser.Span (Span(..))
import           Data.Bifunctor (first)
import           Data.Foldable (toList)
import qualified Data.IntMap as IntMap
import           Data.Semigroup (stimes)
import qualified Data.Text as T
import           Facet.Carrier.Error.Context
import qualified Facet.Core.Expr as CE
import qualified Facet.Core.Module as CM
import qualified Facet.Core.Pattern as CP
import           Facet.Core.Type hiding (bound, global, (.$))
import qualified Facet.Core.Type as CT
import qualified Facet.Env as Env
import           Facet.Name (E, Level(..), MName(..), Name(..), QName(..), T, UName, incrLevel)
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
implicit = Env.fromList [ (N.T (N.TName (T.pack "Type")), MName (T.pack "Facet") ::: Type) ]

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
  -> m Type
unify t1 t2 = t2 <$ go (Level 0) t1 t2
  where
  go n t1 t2 = case (t1, t2) of
    (Type,      Type)       -> pure ()
    (Unit,      Unit)       -> pure ()
    (l1 :* r1,  l2 :* r2)   -> go n l1 l2 *> go n r1 r2
    -- FIXME: we try to unify Type-the-global with Type-the-constant
    -- FIXME: resolve globals to try to progress past certain inequalities
    (f1 :$ a1,  f2 :$ a2)
      | f1 == f2
      , Just _ <- goS a1 a2 -> pure ()
    (a1 :-> b1, a2 :-> b2)  -> go n a1 a2 *> go n b1 b2
    (t1 :=> b1, t2 :=> b2)  -> let v = CT.bound n in go n (ty t1) (ty t2) *> go (incrLevel n) (b1 v) (b2 v)
    -- FIXME: build and display a diff of the root types
    _                       -> couldNotUnify t1 t2
    where
    goS Nil        Nil        = Just (pure ())
    goS (i1 :> l1) (i2 :> l2) = (*>) <$> goS i1 i2 <*> Just (go n l1 l2)
    goS _          _          = Nothing


-- General

switch
  :: Has (Throw P.Print) sig m
  => m (a ::: Type)
  -> Maybe Type
  -> m (a ::: Type)
switch m = \case
  Just _K -> m >>= \ (a ::: _K') -> (a :::) <$> unify _K' _K
  _       -> m

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
elabType (t ::: _K) = go t _K
  where
  go = ST.out >>> \case
    ST.Free  n -> switch $ synth (CT.global <$> global n)
    -- FIXME: there’s no way this is correct
    ST.Bound n -> switch $ synth (CT.bound . Level . id' <$> bound  n)
    ST.Hole  n -> \ _K -> hole (n ::: _K)
    ST.Type    -> switch $ synth _Type
    ST.Void    -> switch $ synth _Void
    ST.Unit    -> switch $ synth _Unit
    t ST.:=> b -> switch $ synth (fmap _check t >~> _check b)
    f ST.:$  a -> switch $ synth (_synth f .$  _check a)
    a ST.:-> b -> switch $ synth (_check a --> _check b)
    l ST.:*  r -> switch $ synth (_check l .*  _check r)
    ST.Loc s b -> local (const s) . go b
    where
    _check r = tm <$> Check (go r . Just)
    _synth r = Synth (go r Nothing)


_Type :: Applicative m => Synth m Type
_Type = Synth $ pure $ Type ::: Type

_Void :: Applicative m => Synth m Type
_Void = Synth $ pure $ Void ::: Type

_Unit :: Applicative m => Synth m Type
_Unit = Synth $ pure $ Unit ::: Type

(.$)
  :: Has (Throw P.Print) sig m
  => Synth m Type
  -> Check m Type
  -> Synth m Type
(.$) = app (CT..$)

infixl 9 .$

(.*)
  :: Applicative m
  => Check m Type
  -> Check m Type
  -> Synth m Type
a .* b = Synth $ do
  a' <- check (a ::: Type)
  b' <- check (b ::: Type)
  pure $ (a' :* b') ::: Type

infixl 7 .*

(-->)
  :: Applicative m
  => Check m Type
  -> Check m Type
  -> Synth m Type
a --> b = Synth $ do
  a' <- check (a ::: Type)
  b' <- check (b ::: Type)
  pure $ (a' :-> b') ::: Type

infixr 2 -->

(>~>)
  :: Has (Reader Context) sig m
  => (Name T ::: Check m Type)
  -> Check m Type
  -> Synth m Type
(n ::: t) >~> b = Synth $ do
  _T <- check (t ::: Type)
  b' <- n ::: _T |- check (b ::: Type)
  -- FIXME: there’s no way this is correct
  pure $ (hint n ::: _T :=> (b' CT..$)) ::: Type

infixr 1 >~>


-- Expressions

elabExpr
  :: Has (Reader Context :+: Reader Env.Env :+: Reader Span :+: Throw P.Print) sig m
  => (SE.Expr ::: Maybe Type)
  -> m (CE.Expr ::: Type)
elabExpr (t ::: _T) = go t _T
  where
  go = SE.out >>> \case
    SE.Free  n -> switch $ synth (CE.Free  <$> global n)
    SE.Bound n -> switch $ synth (CE.Bound <$> bound n)
    SE.Hole  n -> \ _T -> hole (n ::: _T)
    f SE.:$  a -> switch $ synth (_synth f $$ _check a)
    l SE.:*  r -> check (_check l ** _check r) (pretty "product")
    SE.Unit    -> switch $ synth unit
    SE.Comp cs -> check (comp (map (fmap _check) cs)) (pretty "computation")
    SE.Loc s b -> local (const s) . go b
    where
    _check r = tm <$> Check (go r . Just)
    _synth r = Synth (go r Nothing)
    check m msg _T = expectChecked _T msg >>= \ _T -> (::: _T) <$> runCheck m _T


($$)
  :: Has (Throw P.Print) sig m
  => Synth m CE.Expr
  -> Check m CE.Expr
  -> Synth m CE.Expr
($$) = app (CE.:$)

tlam
  :: Has (Reader Context :+: Throw P.Print) sig m
  => UName
  -> Check m CE.Expr
  -> Check m CE.Expr
tlam n b = Check $ \ ty -> do
  (_T, _B) <- expectQuantifiedType (reflow "when checking type lambda") ty
  _T |-- \ v -> CE.TLam n <$> check (b ::: _B v)

lam
  :: Has (Reader Context :+: Throw P.Print) sig m
  => Name E
  -> Check m CE.Expr
  -> Check m CE.Expr
lam n b = Check $ \ _T -> do
  (_A, _B) <- expectFunctionType (reflow "when checking lambda") _T
  n ::: _A |- CE.Lam (CP.Var n) <$> check (b ::: _B)

unit :: Applicative m => Synth m CE.Expr
unit = Synth . pure $ CE.Unit ::: Unit

(**)
  :: Has (Throw P.Print) sig m
  => Check m CE.Expr
  -> Check m CE.Expr
  -> Check m CE.Expr
l ** r = Check $ \ _T -> do
  (_L, _R) <- expectProductType (reflow "when checking product") _T
  l' <- check (l ::: _L)
  r' <- check (r ::: _R)
  pure (l' CE.:* r')

comp
  :: (Has (Reader Context :+: Reader Span :+: Throw P.Print) sig m)
  => [SC.Clause (Check m CE.Expr)]
  -> Check m CE.Expr
comp cs = do
  cs' <- traverse clause cs
  -- FIXME: extend Core to include pattern matching so this isn’t broken
  -- FIXME: extend Core to include computation types
  pure $ head cs'

clause
  :: (Has (Reader Context :+: Reader Span :+: Throw P.Print) sig m)
  => SC.Clause (Check m CE.Expr)
  -> Check m CE.Expr
clause = go
  where
  go = SC.out >>> \case
    SC.Clause p b -> Check $ \ _T -> do
      (_A, _B) <- expectFunctionType (reflow "when checking clause") _T
      p' <- check (pattern p ::: _A)
      foldr (|-) (CE.Lam (tm <$> p') <$> check (go b ::: _B)) p'
    SC.Body e   -> e
    SC.Loc s c  -> local (const s) (go c)


pattern
  :: Has (Reader Span :+: Throw P.Print) sig m
  => SP.Pattern (Name E)
  -> Check m (CP.Pattern (Name E ::: Type))
pattern = go
  where
  go (SP.In s p) = local (const s) $ case p of
    SP.Wildcard -> pure CP.Wildcard
    SP.Var n    -> Check $ \ _T -> pure (CP.Var (n ::: _T))
    SP.Tuple ps -> Check $ \ _T -> CP.Tuple . toList <$> go' _T (fromList ps)
      where
      go' _T = \case
        Nil      -> Nil      <$  unify Unit _T
        Nil :> p -> (Nil :>) <$> check (go p ::: _T)
        ps  :> p -> do
          (_L, _R) <- expectProductType (reflow "when checking tuple pattern") _T
          (:>) <$> go' _L ps <*> check (go p ::: _R)


-- Declarations

elabDecl
  :: Has (Reader Context :+: Reader Env.Env :+: Reader Span :+: Throw P.Print) sig m
  => SD.Decl
  -> m (Check m CE.Expr ::: Type)
elabDecl = go
  where
  go (SD.In s d) = local (const s) $ case d of
    (n ::: t) SD.:=> b -> do
      _T ::: _  <- elabType (t ::: Just Type)
      b' ::: _B <- n ::: _T |- go b
      pure $ tlam (hint n) b' ::: (hint n ::: _T :=> (_B CT..$))

    (n ::: t) SD.:-> b -> do
      _T ::: _  <- elabType (t ::: Just Type)
      b' ::: _B <- n ::: _T |- go b
      pure $ lam n b' ::: (_T :-> _B)

    t SD.:= b -> do
      _T ::: _ <- elabType (t ::: Just Type)
      pure $ _check (elabExpr . (b :::)) ::: _T

  _check r = tm <$> Check (r . Just)


-- Modules

elabModule
  :: Has (Reader Context :+: Reader Env.Env :+: Reader Span :+: Throw P.Print) sig m
  => SM.Module
  -> m CM.Module
-- FIXME: elaborate all the types first, and only then the terms
elabModule (SM.Module s n ds) = local (const s) $ evalState (mempty @Env.Env) $ CM.Module n <$> traverse (elabDef n) ds

elabDef
  :: Has (Reader Context :+: Reader Span :+: State Env.Env :+: Throw P.Print) sig m
  => MName
  -> SM.Def
  -> m (QName, CM.Def ::: Type)
elabDef mname (SM.Def s n d) = local (const s) $ do
  env <- get @Env.Env
  e' ::: _T <- runReader env $ do
    e ::: _T <- elabDecl d
    e' <- check (e ::: _T)
    pure $ e' ::: _T

  modify $ Env.insert (mname :.: n ::: _T)
  -- FIXME: extend the module
  -- FIXME: support defining types
  pure (mname :.: n, CM.DTerm e' ::: _T)


-- Context

(|-) :: Has (Reader Context) sig m => Name b ::: Type -> m a -> m a
n ::: t |- m = local (IntMap.insert (id' n) t) m

infix 1 |-

(|--) :: Has (Reader Context) sig m => UName ::: Type -> (Type -> m a) -> m a
_ ::: t |-- m = do
  i <- asks @Context length
  local (IntMap.insert i t) (m (Right (Level i) :$ Nil)) -- FIXME: this is hopelessly broken, but exists as a temporary workaround until we get the indexing/levelling thing sorted out

infix 1 |--


-- Failures

err :: Has (Throw P.Print) sig m => P.Print -> m a
err = throwError . group

hole :: Has (Throw P.Print) sig m => (T.Text ::: Maybe Type) -> m (a ::: Type)
hole (n ::: t) = case t of
  Just t  -> err $ fillSep [pretty "found", pretty "hole", pretty n, colon, P.printCoreType t]
  Nothing -> couldNotSynthesize (fillSep [ pretty "hole", pretty n ])

mismatch :: Has (Throw P.Print) sig m => P.Print -> P.Print -> P.Print -> m a
mismatch msg exp act = err $ msg
  </> pretty "expected:" <> print exp
  </> pretty "  actual:" <> print act
  where
  -- line things up nicely for e.g. wrapped function types
  print = nest 2 . (flatAlt (line <> stimes (3 :: Int) space) mempty <>)

couldNotUnify :: Has (Throw P.Print) sig m => Type -> Type -> m a
couldNotUnify t1 t2 = mismatch (reflow "mismatch") (P.printCoreType t2) (P.printCoreType t1)

couldNotSynthesize :: Has (Throw P.Print) sig m => P.Print -> m a
couldNotSynthesize msg = err $ reflow "could not synthesize a type for" <> softline <> msg

freeVariable :: Has (Throw P.Print) sig m => P.Print -> m a
freeVariable v = err $ fillSep [reflow "variable not in scope:", v]

expectChecked :: Has (Throw P.Print) sig m => Maybe Type -> P.Print -> m Type
expectChecked t msg = maybe (couldNotSynthesize msg) pure t


-- Patterns

expectMatch :: Has (Throw P.Print) sig m => (Type -> Maybe out) -> P.Print -> P.Print -> Type -> m out
expectMatch pat exp s _T = maybe (mismatch s exp (P.printCoreType _T)) pure (pat _T)

expectQuantifiedType :: Has (Throw P.Print) sig m => P.Print -> Type -> m (UName ::: Type, Type -> Type)
expectQuantifiedType = expectMatch unForAll (pretty "{_} -> _")

expectFunctionType :: Has (Throw P.Print) sig m => P.Print -> Type -> m (Type, Type)
expectFunctionType = expectMatch unArrow (pretty "_ -> _")

expectProductType :: Has (Throw P.Print) sig m => P.Print -> Type -> m (Type, Type)
expectProductType = expectMatch unProduct (pretty "(_, _)")
