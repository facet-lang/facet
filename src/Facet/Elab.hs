{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Elab
( runErrM
, Context
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
import           Control.Effect.Lift
import           Control.Effect.Parser.Span (Span(..))
import           Data.Bifunctor (first)
import           Data.Foldable (toList)
import           Data.Functor.Identity
import           Data.Semigroup (stimes)
import qualified Data.Text as T
import           Data.Traversable (for)
import           Facet.Carrier.Error.Context
import qualified Facet.Core.Expr as CE
import qualified Facet.Core.Module as CM
import qualified Facet.Core.Pattern as CP
import           Facet.Core.Type hiding (bound, global, (.$))
import qualified Facet.Core.Type as CT
import qualified Facet.Env as Env
import           Facet.Error
import           Facet.Name (Index(..), Level(..), QName(..), UName, incrLevel, indexToLevel)
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
import           Silkscreen (colon, fillSep, flatAlt, group, line, nest, pretty, softline, space, (</>))

runErrM :: Span -> ErrorC Span Err Identity a -> Either (Span, Err) a
runErrM s = run . runError (curry (Identity . Left)) (Identity . Right) s

type Context = [UName ::: Type Elab]

elab :: Has (Reader Context :+: Reader (Env.Env Elab) :+: Reader Span :+: Throw Err) sig m => Elab a -> m a
elab (Elab m) = do
  ctx <- ask
  env <- ask
  span <- ask
  run (runError (\ s e -> pure (setSpan s (throwError e))) (pure . pure) span (runReader ctx (runReader env m)))

-- FIXME: can we generalize this to a rank-n quantified action over any context providing these effects?
newtype Elab a = Elab (ReaderC (Env.Env Elab) (ReaderC Context (ErrorC Span Err Identity)) a)
  deriving (Algebra (Reader (Env.Env Elab) :+: Reader Context :+: Error Err :+: Reader Span :+: Lift Identity), Applicative, Functor, Monad)


newtype Check a = Check { runCheck :: Type Elab -> Elab a }
  deriving (Algebra (Reader (Type Elab) :+: Reader (Env.Env Elab) :+: Reader Context :+: Error Err :+: Reader Span :+: Lift Identity), Applicative, Functor, Monad) via ReaderC (Type Elab) Elab

newtype Synth a = Synth { synth :: Elab (a ::: Type Elab) }

instance Functor Synth where
  fmap f (Synth m) = Synth (first f <$> m)

check :: (Check a ::: Type Elab) -> Elab a
check = uncurryAnn runCheck


unify
  :: Type Elab
  -> Type Elab
  -> Elab (Type Elab)
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
    (t1 :=> b1, t2 :=> b2)  -> do
      let v = CT.bound n
      go n (ty t1) (ty t2)
      b1' <- elab $ b1 v
      b2' <- elab $ b2 v
      go (incrLevel n) b1' b2'
    -- FIXME: build and display a diff of the root types
    _                       -> couldNotUnify t1 t2
    where
    goS Nil        Nil        = Just (pure ())
    goS (i1 :> l1) (i2 :> l2) = (*>) <$> goS i1 i2 <*> Just (go n l1 l2)
    goS _          _          = Nothing


-- General

switch
  :: Elab (a ::: Type Elab)
  -> Maybe (Type Elab)
  -> Elab (a ::: Type Elab)
switch m = \case
  Just _K -> m >>= \ (a ::: _K') -> (a :::) <$> unify _K' _K
  _       -> m

global
  :: N.DName
  -> Synth QName
global n = Synth $ asks (Env.lookup n) >>= \case
  Just b  -> pure (tm b :.: n ::: ty b)
  Nothing -> freeVariable (pretty n)

bound
  :: Index
  -> Synth Level
bound n = Synth $ do
  ctx <- ask @Context
  case ctx !? getIndex n of
    Just (_ ::: _T) -> pure (indexToLevel (length ctx) n ::: _T)
    Nothing         -> err (reflow "bad context")

(!?) :: [a] -> Int -> Maybe a
es !? n = go es n
  where
  go (a:as) i
    | i <= 0    = Just a
    | otherwise = go as (i - 1)
  go []     _   = Nothing

app
  :: (a -> a -> a)
  -> Synth a
  -> Check a
  -> Synth a
app ($$) f a = Synth $ do
  f' ::: _F <- synth f
  (_A, _B) <- expectFunctionType (pretty "in application") _F
  a' <- check (a ::: _A)
  pure $ f' $$ a' ::: _B


-- Types

elabType
  :: ST.Type
  -> Maybe (Type Elab)
  -> Elab (Type Elab ::: Type Elab)
elabType = go
  where
  go = ST.out >>> \case
    ST.Free  n -> switch $ synth (CT.global <$> global n)
    ST.Bound n -> switch $ synth (CT.bound <$> bound n)
    ST.Hole  n -> \ _K -> hole (n ::: _K)
    ST.Type    -> switch $ synth _Type
    ST.Void    -> switch $ synth _Void
    ST.Unit    -> switch $ synth _Unit
    t ST.:=> b -> switch $ synth (fmap _check t >~> _check b)
    f ST.:$  a -> switch $ synth (_synth f .$  _check a)
    a ST.:-> b -> switch $ synth (_check a --> _check b)
    l ST.:*  r -> switch $ synth (_check l .*  _check r)
    ST.Loc s b -> setSpan s . go b
    where
    _check r = tm <$> Check (go r . Just)
    _synth r = Synth (go r Nothing)


_Type :: Synth (Type Elab)
_Type = Synth $ pure $ Type ::: Type

_Void :: Synth (Type Elab)
_Void = Synth $ pure $ Void ::: Type

_Unit :: Synth (Type Elab)
_Unit = Synth $ pure $ Unit ::: Type

(.$)
  :: Synth (Type Elab)
  -> Check (Type Elab)
  -> Synth (Type Elab)
f .$ a = Synth $ do
  f' ::: _F <- synth f
  (_A, _B) <- expectFunctionType (pretty "in application") _F
  a' <- check (a ::: _A)
  fa' <- elab $ f' CT..$ a'
  pure $ fa' ::: _B

infixl 9 .$

(.*)
  :: Check (Type Elab)
  -> Check (Type Elab)
  -> Synth (Type Elab)
a .* b = Synth $ do
  a' <- check (a ::: Type)
  b' <- check (b ::: Type)
  pure $ (a' :* b') ::: Type

infixl 7 .*

(-->)
  :: Check (Type Elab)
  -> Check (Type Elab)
  -> Synth (Type Elab)
a --> b = Synth $ do
  a' <- check (a ::: Type)
  b' <- check (b ::: Type)
  pure $ (a' :-> b') ::: Type

infixr 2 -->

(>~>)
  :: (UName ::: Check (Type Elab))
  -> Check (Type Elab)
  -> Synth (Type Elab)
(n ::: t) >~> b = Synth $ do
  _T <- check (t ::: Type)
  b' <- n ::: _T |- check (b ::: Type)
  -- FIXME: there’s no way this is correct
  pure $ (n ::: _T :=> (b' CT..$)) ::: Type

infixr 1 >~>


-- Expressions

elabExpr
  :: SE.Expr
  -> Maybe (Type Elab)
  -> Elab (CE.Expr Elab ::: Type Elab)
elabExpr = go
  where
  go = SE.out >>> \case
    SE.Free  n -> switch $ synth (CE.Free  <$> global n)
    SE.Bound n -> switch $ synth (CE.Bound <$> bound n)
    SE.Hole  n -> \ _T -> hole (n ::: _T)
    f SE.:$  a -> switch $ synth (_synth f $$ _check a)
    l SE.:*  r -> check (_check l ** _check r) (pretty "product")
    SE.Unit    -> switch $ synth unit
    SE.Comp cs -> check (comp (map (fmap _check) cs)) (pretty "computation")
    SE.Loc s b -> setSpan s . go b
    where
    _check r = tm <$> Check (go r . Just)
    _synth r = Synth (go r Nothing)
    check m msg _T = expectChecked _T msg >>= \ _T -> (::: _T) <$> runCheck m _T


($$)
  :: Synth (CE.Expr Elab)
  -> Check (CE.Expr Elab)
  -> Synth (CE.Expr Elab)
($$) = app (CE.:$)

tlam
  :: UName
  -> Check (CE.Expr Elab)
  -> Check (CE.Expr Elab)
tlam n b = Check $ \ ty -> do
  (_T, _B) <- expectQuantifiedType (reflow "when checking type lambda") ty
  pure (CE.TLam n (\ v -> _T |- do
    _B' <- elab (_B v)
    check (b ::: _B')))

lam
  :: UName
  -> Check (CE.Expr Elab)
  -> Check (CE.Expr Elab)
lam n b = Check $ \ _T -> do
  (_A, _B) <- expectFunctionType (reflow "when checking lambda") _T
  n ::: _A |- do
    -- FIXME: this is wrong, we should check under the binder
    b' <- check (b ::: _B)
    pure (CE.Lam (CP.Var n) (pure . (b' CE.:$)))

unit :: Synth (CE.Expr Elab)
unit = Synth . pure $ CE.Unit ::: Unit

(**)
  :: Check (CE.Expr Elab)
  -> Check (CE.Expr Elab)
  -> Check (CE.Expr Elab)
l ** r = Check $ \ _T -> do
  (_L, _R) <- expectProductType (reflow "when checking product") _T
  l' <- check (l ::: _L)
  r' <- check (r ::: _R)
  pure (l' CE.:* r')

comp
  :: [SC.Clause (Check (CE.Expr Elab))]
  -> Check (CE.Expr Elab)
comp cs = do
  cs' <- traverse clause cs
  -- FIXME: extend Core to include pattern matching so this isn’t broken
  -- FIXME: extend Core to include computation types
  pure $ head cs'

clause
  :: SC.Clause (Check (CE.Expr Elab))
  -> Check (CE.Expr Elab)
clause = go
  where
  go = SC.out >>> \case
    SC.Clause p b -> Check $ \ _T -> do
      (_A, _B) <- expectFunctionType (reflow "when checking clause") _T
      p' <- check (pattern p ::: _A)
      foldr (|-) (do
        -- FIXME: this is wrong.
        b' <- check (go b ::: _B)
        pure (CE.Lam (tm <$> p') (pure . (b' CE.:$)))) p'
    SC.Body e   -> e
    SC.Loc s c  -> setSpan s (go c)


pattern
  :: SP.Pattern (UName)
  -> Check (CP.Pattern (UName ::: Type Elab))
pattern = go
  where
  go (SP.In s p) = setSpan s $ case p of
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
  :: SD.Decl
  -> Check (CE.Expr Elab) ::: Check (Type Elab)
elabDecl = go
  where
  go (SD.In s d) = setSpans s $ case d of
    (n ::: t) SD.:=> b ->
      let b' ::: _B = go b
      in tlam n b' ::: _check (switch (synth (n ::: _check (elabType t) >~> _B)))

    (n ::: t) SD.:-> b ->
      let b' ::: _B = go b
      in lam n b' ::: _check (switch (synth (_check (elabType t) --> _B)))

    t SD.:= b ->
      _check (elabExpr b) ::: _check (elabType t)

  _check r = tm <$> Check (r . Just)

  setSpans s (t ::: _T) = setSpan s t ::: setSpan s _T


-- Modules

elabModule
  :: Has (Reader Span :+: Throw Err) sig m
  => SM.Module
  -> m (CM.Module Elab)
elabModule (SM.Module s mname ds) = setSpan s . evalState (mempty @(Env.Env Elab)) $ do
  -- FIXME: elaborate all the types first, and only then the terms
  -- FIXME: maybe figure out the graph for mutual recursion?
  defs <- for ds $ \ (SM.Def s n d) -> setSpan s $ do
    env <- get @(Env.Env Elab)
    e' ::: _T <- runReader @Context [] . runReader env $ do
      let e ::: t = elabDecl d
      _T <- elab $ check (t ::: Type)
      e' <- elab $ check (e ::: _T)
      pure $ e' ::: _T

    modify $ Env.insert (mname :.: n ::: _T)
    -- FIXME: extend the module
    -- FIXME: support defining types
    pure (mname :.: n, CM.DTerm e' ::: _T)

  pure $ CM.Module mname defs


-- Context

(|-) :: Has (Reader Context) sig m => UName ::: Type Elab -> m a -> m a
t |- m = local (t:) m

infix 1 |-


-- Failures

setSpan :: Has (Reader Span) sig m => Span -> m a -> m a
setSpan = local . const

printType :: Has (Reader Context :+: Reader (Env.Env Elab) :+: Reader Span :+: Throw Err) sig m => Type Elab -> m ErrDoc
-- FIXME: this is almost certainly going to show the wrong thing because we don’t incorporate types from the context
printType t = P.getPrint <$> elab (P.printCoreType t)

err :: Has (Throw Err) sig m => ErrDoc -> m a
err = throwError . (`Err` []) . group

hole :: Has (Reader Context :+: Reader (Env.Env Elab) :+: Reader Span :+: Throw Err) sig m => (T.Text ::: Maybe (Type Elab)) -> m (a ::: Type Elab)
hole (n ::: t) = case t of
  Just t  -> do
    t' <- printType t
    err $ fillSep [pretty "found", pretty "hole", pretty n, colon, t' ]
  Nothing -> couldNotSynthesize (fillSep [ pretty "hole", pretty n ])

mismatch :: Has (Throw Err) sig m => ErrDoc -> ErrDoc -> ErrDoc -> m a
mismatch msg exp act = err $ msg
  </> pretty "expected:" <> print exp
  </> pretty "  actual:" <> print act
  where
  -- line things up nicely for e.g. wrapped function types
  print = nest 2 . (flatAlt (line <> stimes (3 :: Int) space) mempty <>)

couldNotUnify :: Has (Reader Context :+: Reader (Env.Env Elab) :+: Reader Span :+: Throw Err) sig m => Type Elab -> Type Elab -> m a
couldNotUnify t1 t2 = do
  t1' <- printType t1
  t2' <- printType t2
  mismatch (reflow "mismatch") t2' t1'

couldNotSynthesize :: Has (Throw Err) sig m => ErrDoc -> m a
couldNotSynthesize msg = err $ reflow "could not synthesize a type for" <> softline <> msg

freeVariable :: Has (Throw Err) sig m => ErrDoc -> m a
freeVariable v = err $ fillSep [reflow "variable not in scope:", v]

expectChecked :: Has (Throw Err) sig m => Maybe (Type Elab) -> ErrDoc -> m (Type Elab)
expectChecked t msg = maybe (couldNotSynthesize msg) pure t


-- Patterns

expectMatch :: Has (Reader Context :+: Reader (Env.Env Elab) :+: Reader Span :+: Throw Err) sig m => (Type Elab -> Maybe out) -> ErrDoc -> ErrDoc -> Type Elab -> m out
expectMatch pat exp s _T = do
  _T' <- printType _T
  maybe (mismatch s exp _T') pure (pat _T)

expectQuantifiedType :: Has (Reader Context :+: Reader (Env.Env Elab) :+: Reader Span :+: Throw Err) sig m => ErrDoc -> Type Elab -> m (UName ::: Type Elab, Type Elab -> Elab (Type Elab))
expectQuantifiedType = expectMatch unForAll (pretty "{_} -> _")

expectFunctionType :: Has (Reader Context :+: Reader (Env.Env Elab) :+: Reader Span :+: Throw Err) sig m => ErrDoc -> Type Elab -> m (Type Elab, Type Elab)
expectFunctionType = expectMatch unArrow (pretty "_ -> _")

expectProductType :: Has (Reader Context :+: Reader (Env.Env Elab) :+: Reader Span :+: Throw Err) sig m => ErrDoc -> Type Elab -> m (Type Elab, Type Elab)
expectProductType = expectMatch unProduct (pretty "(_, _)")
