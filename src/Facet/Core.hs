{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core
( -- * Values
  Value(..)
, Head(Global, Free, Metavar)
, Elim(..)
, unHead
, global
, free
, metavar
, unForAll
, unForAll'
, unLam
, unLam'
, ($$)
, case'
, match
, handleBinder
, handleBinderP
, subst
, AValue(..)
, Contextual(..)
  -- * Patterns
, Pattern(..)
  -- * Modules
, Module(..)
, Def(..)
  -- * Quotation
, QExpr(..)
, quote
, eval
) where

import           Control.Effect.Empty
import           Data.Bifoldable
import           Data.Bifunctor
import           Data.Bitraversable
import           Data.Foldable (foldl', toList)
import           Data.Functor (void)
import qualified Data.IntMap as IntMap
import           Data.Monoid (First(..))
import           Data.Traversable (mapAccumL)
import qualified Facet.Context as Ctx
import           Facet.Name (CName, Index(..), Level(..), MName, Meta(..), QName, UName, levelToIndex)
import           Facet.Stack
import           Facet.Syntax
import           GHC.Stack

-- Values

-- FIXME: represent closed portions of the tree explicitly?
data Value a
  = Type
  | (Pl_ UName ::: Value a) :=> (Value a -> Value a)
  -- FIXME: consider type-indexed patterns & an existential clause wrapper to ensure name & variable patterns have the same static shape
  | Lam (Pl_ UName ::: Value a) (Value a -> Value a)
  -- | Neutral terms are an unreduced head followed by a stack of eliminators.
  | Neut (Head Level a) (Stack (Elim (Value a)))
  | VCon (QName ::: Value a) (Stack (Value a))

infixr 1 :=>

instance (Eq a, Num a) => Eq (Value a) where
  v1 == v2 = go 0 v1 v2
    where
    -- defined thus to get the exhaustiveness checker to ensure I don’t miss adding new cases
    go n = curry $ \case
      (Type, Type) -> True
      (Type, _) -> False
      (t1 :=> b1, t2 :=> b2) ->
        pl (tm t1) == pl (tm t2) && go n (ty t1) (ty t2)
        &&  let b1' = b1 (free n)
                b2' = b2 (free n)
            in go (n + 1) b1' b2'
      (_ :=> _, _) -> False
      (Lam _ b1, Lam _ b2) ->
        let b1' = b1 (free n)
            b2' = b2 (free n)
        in go (n + 1) b1' b2'
      (Lam _ _, _) -> False
      (Neut h1 sp1, Neut h2 sp2) -> h1 == h2 && eqSp n sp1 sp2
      (Neut _ _, _) -> False
      (VCon n1 p1, VCon n2 p2)
        | length p1 == length p2 -> go n (ty n1) (ty n2) && and (zipWith (go n) (toList p1) (toList p2))
      (VCon _ _, _) -> False

    eqSp n (sp1:>e1) (sp2:>e2) = eqSp n sp1 sp2 && eqElim n e1 e2
    eqSp _ Nil       Nil       = True
    eqSp _ _         _         = False
    eqElim n = curry $ \case
      (App a1, App a2) -> pl a1 == pl a2 && go n (out a1) (out a2)
      (App _, _) -> False
      (Case cs1, Case cs2)
        | length cs1 == length cs2 -> and (zipWith (eqPat n) (toList cs1) (toList cs2))
      (Case _, _) -> False
    eqPat n (p1, b1) (p2, b2)
      =   void p1 == void p2
      &&  let (n', p') = mapAccumL (\ n _ -> (n + 1, free n)) n p2
              b1' = b1 p'
              b2' = b2 p'
          in go n' b1' b2'


data Head a b
  = Global (QName ::: Value b) -- ^ Global variables, considered equal by 'QName'.
  | Free b
  | Bound a
  | Metavar (Meta ::: Value b) -- ^ Metavariables, considered equal by 'Level'.

instance (Eq a, Eq b) => Eq (Head a b) where
  Global q1  == Global q2  = tm q1 == tm q2
  Global _   == _          = False
  Free a1    == Free a2    = a1 == a2
  Free _     == _          = False
  Bound l1   == Bound l2   = l1 == l2
  Bound _    == _          = False
  Metavar m1 == Metavar m2 = tm m1 == tm m2
  Metavar _  == _          = False

unHead :: (QName ::: Value b -> c) -> (b -> c) -> (a -> c) -> (Meta ::: Value b -> c) -> Head a b -> c
unHead f g h i = \case
  Global  n -> f n
  Free    n -> g n
  Bound   n -> h n
  Metavar n -> i n


data Elim a
  = App (Pl_ a) -- FIXME: this is our one codata case; should we generalize this to copattern matching?
  | Case [(Pattern a (UName ::: a), Pattern a a -> a)]


global :: QName ::: Value a -> Value a
global = var . Global

free :: a -> Value a
free = var . Free

metavar :: Meta ::: Value a -> Value a
metavar = var . Metavar


var :: Head Level a -> Value a
var = (`Neut` Nil)


unForAll :: Has Empty sig m => Value a -> m (Pl_ UName ::: Value a, Value a -> Value a)
unForAll = \case{ t :=> b -> pure (t, b) ; _ -> empty }

-- | A variation on 'unForAll' which can be conveniently chained with 'splitr' to strip a prefix of quantifiers off their eventual body.
unForAll' :: Has Empty sig m => (Level -> Pl_ UName ::: Value a -> a) -> (Level, Value a) -> m ((Level, Pl_ UName ::: Value a), (Level, Value a))
unForAll' var (d, v) = do
  (_T, _B) <- unForAll v
  pure ((d, _T), (succ d, _B (free (var d _T))))

unLam :: Has Empty sig m => Value a -> m (Pl_ UName ::: Value a, Value a -> Value a)
unLam = \case{ Lam n b -> pure (n, b) ; _ -> empty }

-- | A variation on 'unLam' which can be conveniently chained with 'splitr' to strip a prefix of lambdas off their eventual body.
unLam' :: Has Empty sig m => (Level -> Pl_ UName ::: Value a -> a) -> (Level, Value a) -> m ((Level, Pl_ UName ::: Value a), (Level, Value a))
unLam' var (d, v) = do
  (n, t) <- unLam v
  pure ((d, n), (succ d, t (free (var d n))))


-- FIXME: how should this work in weak/parametric HOAS?
($$) :: HasCallStack => Value a -> Pl_ (Value a) -> Value a
Neut h es $$ a = Neut h (es :> App a)
(_ :=> b) $$ a = b (out a)
Lam _  b  $$ a = b (out a)
_         $$ _ = error "can’t apply non-neutral/forall type"

infixl 9 $$


case' :: HasCallStack => Value a -> [(Pattern (Value a) (UName ::: Value a), Pattern (Value a) (Value a) -> Value a)] -> Value a
case' (Neut h es) cs = Neut h (es :> Case cs)
case' s           cs = case getFirst (foldMap (\ (p, f) -> First $ f <$> match s p) cs) of
  Just v -> v
  _      -> error "non-exhaustive patterns in lambda"

match :: Value a -> Pattern (Value a) b -> Maybe (Pattern (Value a) (Value a))
match = curry $ \case
  (_,          Wildcard)       -> Just Wildcard
  (s,          Var _)          -> Just (Var s)
  (VCon n' fs, Con n ps)       -> do
    guard (tm n == tm n')
    -- NB: we’re assuming they’re the same length because they’ve passed elaboration.
    Con n' <$> sequenceA (zipWith match (toList fs) ps)
  (_,          Con _ _)        -> Nothing


elim :: HasCallStack => Value a -> Elim (Value a) -> Value a
elim v = \case
  App a   -> v $$ a
  Case cs -> case' v cs

elimN :: (HasCallStack, Foldable t) => Value a -> t (Elim (Value a)) -> Value a
elimN f as = foldl' elim f as


handleBinder :: (HasCallStack, Monad m) => Meta ::: Value a -> (Value a -> m (Value a)) -> m (Value a -> Value a)
handleBinder d b = do
  b' <- b (metavar d)
  pure $ (`subst` b') . IntMap.singleton (getMeta (tm d))

handleBinderP :: (HasCallStack, Monad m, Traversable t) => t (Meta ::: Value a) -> (t (Value a) -> m (Value a)) -> m (t (Value a) -> Value a)
handleBinderP p b = do
  b' <- b (metavar <$> p)
  pure $ \ v -> subst (foldl' (\ s (m ::: _, v) -> IntMap.insert (getMeta m) v s) IntMap.empty (zip (toList p) (toList v))) b'

-- | Substitute metavars.
subst :: HasCallStack => IntMap.IntMap (Value a) -> Value a -> Value a
subst s
  | IntMap.null s = id
  | otherwise     = go
  where
  go = \case
    Type     -> Type
    t :=> b  -> fmap go t :=> go . b
    Lam n b  -> Lam (fmap go n) (go . b)
    Neut f a -> unHead global free (var . Bound) (s !) f' `elimN` fmap substElim a
      where
      f' = case f of
        Global  (n ::: _T) -> Global  (n ::: go _T)
        Free    v          -> Free    v
        Bound   v          -> Bound   v
        Metavar (d ::: _T) -> Metavar (d ::: go _T)
    VCon n p -> VCon (fmap go n) (fmap go p)

  substElim = \case
    App a   -> App (fmap go a)
    Case cs -> Case (map (bimap (bimap go (fmap go)) (go .)) cs)

  s ! l = case IntMap.lookup (getMeta (tm l)) s of
    Just a  -> a
    Nothing -> metavar l


newtype AValue = AValue { runAValue :: forall x . Value x }

instance Eq AValue where
  v1 == v2 = (runAValue v1 :: Value Int) == (runAValue v2)


newtype Contextual f = Contextual { runContextual :: forall x . Ctx.Context (Value x ::: Value x) :|-: f x }


-- Patterns

-- FIXME: represent wildcard patterns as var patterns with an empty name.
data Pattern t a
  = Wildcard
  | Var a
  | Con (QName ::: t) [Pattern t a]
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bifoldable Pattern where
  bifoldMap = bifoldMapDefault

instance Bifunctor Pattern where
  bimap = bimapDefault

instance Bitraversable Pattern where
  bitraverse f g = go
    where
    go = \case
      Wildcard -> pure Wildcard
      Var a -> Var <$> g a
      Con (n ::: t) ps -> Con . (n :::) <$> f t <*> traverse go ps


-- Modules

data Module a = Module MName [(QName, Def a ::: Value a)]

data Def a
  = DTerm (Value a)
  | DType (Value a)
  | DData [CName ::: Value a]


-- Quotation

data QExpr a
  = QGlobal (QName ::: QExpr a)
  | QVar Index
  | QFree a
  | QMeta (Meta ::: QExpr a)
  | QType
  | QForAll (Pl_ UName ::: QExpr a) (QExpr a)
  | QLam (Pl_ UName ::: (QExpr a)) (QExpr a)
  | QApp (QExpr a) (Pl_ (QExpr a))
  | QCase (QExpr a) [(Pattern (QExpr a) (UName ::: QExpr a), QExpr a)]
  | QCon (QName ::: QExpr a) (Stack (QExpr a))
  deriving (Eq, Ord, Show)

quote :: Level -> Value a -> QExpr a
quote d = \case
  Type -> QType
  VCon (n ::: t) fs -> QCon (n ::: quote d t) (fmap (quote d) fs)
  Lam (n ::: t) b -> QLam (n ::: quote d t) (quote (succ d) (b (var (Bound d))))
  n ::: t :=> b -> QForAll (n ::: quote d t) (quote (succ d) (b (var (Bound d))))
  Neut h sp ->
    let qSp h Nil     = h
        qSp h (sp:>e) = case e of
          App a   -> QApp (qSp h sp) (fmap (quote d) a)
          Case cs -> QCase (qSp h sp) (map qClause cs)
        qClause (p, b)
          | let (d', p') = mapAccumL (\ d _ -> (succ d, var (Bound d))) d p
          = ( bimap (quote d) (fmap (quote d)) p
            , quote d' (b p'))
    in qSp (unHead (QGlobal . fmap (quote d)) QFree (QVar . levelToIndex d) (QMeta . fmap (quote d)) h) sp

eval :: Stack (Value a) -> QExpr a -> Value a
eval env = \case
  QType -> Type
  QCon (n ::: t) fs -> VCon (n ::: eval env t) (fmap (eval env) fs)
  QLam (n ::: t) b -> Lam (n ::: eval env t) (\ v -> eval (env:>v) b)
  QForAll (n ::: t) b -> n ::: eval env t :=> \ v -> eval (env:>v) b
  QGlobal (n ::: t) -> global (n ::: eval env t)
  QFree a -> free a
  QVar n -> env ! getIndex n
  QMeta (n ::: t) -> metavar (n ::: eval env t)
  QApp f a -> eval env f $$ fmap (eval env) a
  QCase s cs -> case' (eval env s) (map (evalClause env) cs)
    where
    evalClause env (p, b) = (bimap (eval env) (fmap (eval env)) p, \ p -> eval (foldl' (:>) env p) b)
