{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core
( -- * Values
  Value(..)
, Head(..)
, Elim(..)
, Con(..)
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
import           Data.Semialign
import           Data.Traversable (mapAccumL)
import           Facet.Name (CName, Index(..), Level(..), MName, Meta(..), QName, UName, levelToIndex)
import           Facet.Stack
import           Facet.Syntax
import           GHC.Stack
import           Prelude hiding (zip, zipWith)

-- Values

-- FIXME: represent closed portions of the tree explicitly?
data Value
  = Type
  | (Pl_ UName ::: Value) :=> (Value -> Value)
  -- FIXME: consider type-indexed patterns & an existential clause wrapper to ensure name & variable patterns have the same static shape
  | Lam (Pl_ UName ::: Value) (Value -> Value)
  -- | Neutral terms are an unreduced head followed by a stack of eliminators.
  | Neut (Head Value Level) (Stack Elim)
  | VCon (Con Value Value)

infixr 1 :=>

instance Eq Value where
  v1 == v2 = go (Level 0) v1 v2
    where
    -- defined thus to get the exhaustiveness checker to ensure I don’t miss adding new cases
    go n = curry $ \case
      (Type, Type) -> True
      (Type, _) -> False
      (t1 :=> b1, t2 :=> b2) ->
        pl (tm t1) == pl (tm t2) && go n (ty t1) (ty t2)
        &&  let b1' = b1 (free n)
                b2' = b2 (free n)
            in go (succ n) b1' b2'
      (_ :=> _, _) -> False
      (Lam _ b1, Lam _ b2) ->
        let b1' = b1 (free n)
            b2' = b2 (free n)
        in go (succ n) b1' b2'
      (Lam _ _, _) -> False
      (Neut h1 sp1, Neut h2 sp2) -> h1 == h2 && eqSp n sp1 sp2
      (Neut _ _, _) -> False
      (VCon (Con n1 p1), VCon (Con n2 p2))
        | length p1 == length p2 -> go n (ty n1) (ty n2) && and (zipWith (go n) (toList p1) (toList p2))
      (VCon _, _) -> False

    eqSp n (sp1:>e1) (sp2:>e2) = eqSp n sp1 sp2 && eqElim n e1 e2
    eqSp _ Nil       Nil       = True
    eqSp _ _         _         = False
    eqElim n = curry $ \case
      (EApp a1, EApp a2) -> pl a1 == pl a2 && go n (out a1) (out a2)
      (EApp _, _) -> False
      (ECase cs1, ECase cs2)
        | length cs1 == length cs2 -> and (zipWith (eqPat n) (toList cs1) (toList cs2))
      (ECase _, _) -> False
    eqPat n (p1, b1) (p2, b2)
      =   void p1 == void p2
      &&  let (n', p') = mapAccumL (\ n _ -> (succ n, free n)) n p2
          in go n' (b1 p') (b2 p')


data Head t a
  = Global (QName ::: t) -- ^ Global variables, considered equal by 'QName'.
  | Free a
  | Metavar (Meta ::: t) -- ^ Metavariables, considered equal by 'Level'.
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

unHead :: (QName ::: t -> b) -> (a -> b) -> (Meta ::: t -> b) -> Head t a -> b
unHead f g h = \case
  Global  n -> f n
  Free    n -> g n
  Metavar n -> h n


data Elim
  = EApp (Pl_ Value) -- FIXME: this is our one codata case; should we generalize this to copattern matching?
  | ECase [(Pattern Value (UName ::: Value), Pattern Value Value -> Value)] -- FIXME: we can (and should) eliminate var patterns eagerly.


data Con t a = Con (QName ::: t) (Stack a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bifoldable Con where
  bifoldMap = bifoldMapDefault

instance Bifunctor Con where
  bimap = bimapDefault

instance Bitraversable Con where
  bitraverse f g (Con t b) = Con <$> traverse f t <*> traverse g b


global :: QName ::: Value -> Value
global = var . Global

free :: Level -> Value
free = var . Free

metavar :: Meta ::: Value -> Value
metavar = var . Metavar


var :: Head Value Level -> Value
var = (`Neut` Nil)


unForAll :: Has Empty sig m => Value -> m (Pl_ UName ::: Value, Value -> Value)
unForAll = \case{ t :=> b -> pure (t, b) ; _ -> empty }

-- | A variation on 'unForAll' which can be conveniently chained with 'splitr' to strip a prefix of quantifiers off their eventual body.
unForAll' :: Has Empty sig m => (Level, Value) -> m (Pl_ UName ::: Value, (Level, Value))
unForAll' (d, v) = do
  (_T, _B) <- unForAll v
  pure (_T, (succ d, _B (free d)))

unLam :: Has Empty sig m => Value -> m (Pl_ UName ::: Value, Value -> Value)
unLam = \case{ Lam n b -> pure (n, b) ; _ -> empty }

-- | A variation on 'unLam' which can be conveniently chained with 'splitr' to strip a prefix of lambdas off their eventual body.
unLam' :: Has Empty sig m => (Level, Value) -> m (Pl_ UName ::: Value, (Level, Value))
unLam' (d, v) = do
  (n, t) <- unLam v
  pure (n, (succ d, t (free d)))


-- FIXME: how should this work in weak/parametric HOAS?
($$) :: HasCallStack => Value -> Pl_ Value -> Value
Neut h es $$ a = Neut h (es :> EApp a)
(_ :=> b) $$ a = b (out a)
Lam _  b  $$ a = b (out a)
_         $$ _ = error "can’t apply non-neutral/forall type"

infixl 9 $$


case' :: HasCallStack => Value -> [(Pattern Value (UName ::: Value), Pattern Value Value -> Value)] -> Value
case' (Neut h es) cs = Neut h (es :> ECase cs)
case' s           cs = case getFirst (foldMap (\ (p, f) -> First $ f <$> match s p) cs) of
  Just v -> v
  _      -> error "non-exhaustive patterns in lambda"

match :: Value -> Pattern Value b -> Maybe (Pattern Value Value)
match = curry $ \case
  (s,          PVar _)                -> Just (PVar s)
  (VCon (Con n' fs), PCon (Con n ps)) -> do
    guard (tm n == tm n')
    -- NB: we’re assuming they’re the same length because they’ve passed elaboration.
    PCon . Con n' <$> sequenceA (zipWith match fs ps)
  (_,          PCon _)                -> Nothing


elim :: HasCallStack => Value -> Elim -> Value
elim v = \case
  EApp a   -> v $$ a
  ECase cs -> case' v cs

elimN :: (HasCallStack, Foldable t) => Value -> t Elim -> Value
elimN f as = foldl' elim f as


handleBinder :: (HasCallStack, Monad m) => Meta ::: Value -> (Value -> m Value) -> m (Value -> Value)
handleBinder d b = do
  b' <- b (metavar d)
  pure $ (`subst` b') . IntMap.singleton (getMeta (tm d))

handleBinderP :: (HasCallStack, Monad m, Traversable t) => t (Meta ::: Value) -> (t Value -> m Value) -> m (t Value -> Value)
handleBinderP p b = do
  b' <- b (metavar <$> p)
  pure $ \ v -> subst (foldl' (\ s (m ::: _, v) -> IntMap.insert (getMeta m) v s) IntMap.empty (zip (toList p) (toList v))) b'

-- | Substitute metavars.
subst :: HasCallStack => IntMap.IntMap Value -> Value -> Value
subst s
  | IntMap.null s = id
  | otherwise     = go
  where
  go = \case
    Type     -> Type
    t :=> b  -> fmap go t :=> go . b
    Lam n b  -> Lam (fmap go n) (go . b)
    Neut f a -> unHead global free (s !) f' `elimN` fmap substElim a
      where
      f' = case f of
        Global  (n ::: _T) -> Global  (n ::: go _T)
        Free    v          -> Free    v
        Metavar (d ::: _T) -> Metavar (d ::: go _T)
    VCon c   -> VCon (bimap go go c)

  substElim = \case
    EApp a   -> EApp (fmap go a)
    ECase cs -> ECase (map (bimap (bimap go (fmap go)) (go .)) cs)

  s ! l = case IntMap.lookup (getMeta (tm l)) s of
    Just a  -> a
    Nothing -> metavar l


-- Patterns

data Pattern t a
  = PVar a
  | PCon (Con t (Pattern t a))
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bifoldable Pattern where
  bifoldMap = bifoldMapDefault

instance Bifunctor Pattern where
  bimap = bimapDefault

instance Bitraversable Pattern where
  bitraverse f g = go
    where
    go = \case
      PVar a -> PVar <$> g a
      PCon c -> PCon <$> bitraverse f go c


-- Modules

data Module = Module MName [(QName, Def ::: Value)]

data Def
  = DTerm Value
  | DType Value
  | DData [CName ::: Value]


-- Quotation

data QExpr
  = QVar (Head QExpr Index)
  | QType
  | QForAll (Pl_ UName ::: QExpr) QExpr
  | QLam (Pl_ UName ::: QExpr) QExpr
  | QApp QExpr (Pl_ QExpr)
  | QCase QExpr [(Pattern QExpr (UName ::: QExpr), QExpr)]
  | QCon (Con QExpr QExpr)
  deriving (Eq, Ord, Show)

quote :: Level -> Value -> QExpr
quote d = \case
  Type -> QType
  VCon c -> QCon (bimap (quote d) (quote d) c)
  Lam (n ::: t) b -> QLam (n ::: quote d t) (quote (succ d) (b (var (Free d))))
  n ::: t :=> b -> QForAll (n ::: quote d t) (quote (succ d) (b (var (Free d))))
  Neut h sp ->
    let qSp h Nil     = h
        qSp h (sp:>e) = case e of
          EApp a   -> QApp (qSp h sp) (fmap (quote d) a)
          ECase cs -> QCase (qSp h sp) (map qClause cs)
        qClause (p, b)
          | let (d', p') = mapAccumL (\ d _ -> (succ d, var (Free d))) d p
          = ( bimap (quote d) (fmap (quote d)) p
            , quote d' (b p'))
    in qSp (QVar (unHead (Global . fmap (quote d)) (Free . levelToIndex d) (Metavar . fmap (quote d)) h)) sp

eval :: Stack Value -> QExpr -> Value
eval env = \case
  QType -> Type
  QCon c -> VCon (bimap (eval env) (eval env) c)
  QLam (n ::: t) b -> Lam (n ::: eval env t) (\ v -> eval (env:>v) b)
  QForAll (n ::: t) b -> n ::: eval env t :=> \ v -> eval (env:>v) b
  QVar h -> unHead (global . fmap (eval env)) ((env !) . getIndex) (metavar . fmap (eval env)) h
  QApp f a -> eval env f $$ fmap (eval env) a
  QCase s cs -> case' (eval env s) (map (evalClause env) cs)
    where
    evalClause env (p, b) = (bimap (eval env) (fmap (eval env)) p, \ p -> eval (foldl' (:>) env p) b)
