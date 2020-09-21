{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Facet.Syntax.Examples
( -- * Examples
  prelude
, id'
, const'
, flip'
, curry'
, uncurry'
, get
, put
, runState
, execState
, postIncr
, empty
, runEmpty
, execEmpty
  -- * Effects
, State(..)
, Empty(..)
) where

import Facet.Syntax.Typed

prelude :: Module expr ty decl mod => mod ()
prelude = do
  "id" .: forAll $ \ _A
    -> _A >-> \ x -> _A
    .= x
  "const" .: forAll $ \ _A -> forAll $ \ _B
    -> _A >-> \ x -> _B --> _A
    .= lam0 (const x)
  "unit" .: _Unit .= pure ()
  "flip" .: forAll $ \ _A -> forAll $ \ _B -> forAll $ \ _C
    -> (_A --> _B --> _C) >-> \ f -> _B >-> \ b -> _A >-> \ a -> _C
    .= f $$ a $$ b
  "curry" .: forAll $ \ _A -> forAll $ \ _B -> forAll $ \ _C
    -> ((_A .* _B) --> _C) >-> \ f -> _A >-> \ a -> _B >-> \ b -> _C
    .= f $$ ((,) <$> a <*> b)
  "curry" .: forAll $ \ _A -> forAll $ \ _B -> forAll $ \ _C
    -> (_A --> _B --> _C) >-> \ f -> _A .* _B >-> \ ab -> _C
    .= f $$ (fst <$> ab) $$ (snd <$> ab)
  pure ()


id' :: Expr repr => repr sig (repr sig a -> repr sig a)
id' = lam0 val

const' :: Expr repr => repr sig (repr sig a -> repr sig (repr sig b -> repr sig a))
const' = lam0 (lam0 . const . val)

flip' :: Expr repr => repr sig (repr sig (repr sig a -> repr sig (repr sig b -> repr sig c)) -> repr sig (repr sig b -> repr sig (repr sig a -> repr sig c)))
flip' = lam0 (\ f -> lam0 (\ b -> lam0 (\ a -> val f $$ val a $$ val b)))

curry' :: Expr repr => repr sig (repr sig (repr sig (a, b) -> repr sig c) -> repr sig (repr sig a -> repr sig (repr sig b -> repr sig c)))
curry' = lam0 $ \ f -> lam0 $ \ a -> lam0 $ \ b -> val f $$ ((,) <$> val a <*> val b)

uncurry' :: Expr repr => repr sig (repr sig (repr sig a -> repr sig (repr sig b -> repr sig c)) -> repr sig (repr sig (a, b) -> repr sig c))
uncurry' = lam0 $ \ f -> lam0 $ \ ab -> val f $$ fmap fst (val ab) $$ fmap snd (val ab)

get :: (Expr repr, Member (State (repr None s)) sig) => repr sig s
get = alg (Inst (inj Get) val)

put :: (Expr repr, Member (State (repr None s)) sig) => repr sig (repr sig s -> repr sig ())
put = lam0 $ \ s -> alg (Inst (inj (Put s)) pure)

runState :: Expr repr => repr sig (repr sig s -> repr sig (repr (Sum (State (repr None s)) sig) a -> repr sig (s, a)))
runState = lam0 $ \ s -> lam $ \case
  Left a                -> (,) <$> val s <*> val a
  Right (Inst Get     k) -> runState $$ val s $$ k s
  Right (Inst (Put s) k) -> runState $$ val s $$ k ()

execState :: Expr repr => repr sig (repr sig s -> repr sig (repr (Sum (State (repr None s)) sig) a -> repr sig a))
execState = lam0 $ \ s -> lam $ \case
  Left a                -> val a
  Right (Inst Get     k) -> execState $$ val s $$ k s
  Right (Inst (Put s) k) -> execState $$ val s $$ k ()


postIncr :: forall repr sig . (Expr repr, Num (repr sig Int), Member (State (repr None Int)) sig) => repr sig Int
postIncr = get <& put $$ (get + 1 :: repr sig Int)


empty :: (Expr repr, Member Empty sig) => repr sig a
empty = alg (Inst (inj Empty) pure)

runEmpty :: Expr repr => repr sig (repr sig a -> repr sig (repr (Sum Empty sig) a -> repr sig a))
runEmpty = lam0 $ \ a -> lam $ \case
  Left x               -> val x
  Right (Inst Empty _) -> val a

execEmpty :: Expr repr => repr sig (repr (Sum Empty sig) a -> repr sig Bool)
execEmpty = lam (either (const (pure True)) (const (pure False)))


-- Effects

data State s k where
  Get :: State s s
  Put :: s -> State s ()

data Empty k = Empty
