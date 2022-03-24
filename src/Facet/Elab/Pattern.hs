{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Elab.Pattern
( Pattern(..)
, Clause(..)
, patterns_
, Type(..)
, Branch(..)
, (\/)
  -- * Coverage judgement
, Covers(..)
, covers
, coverLoop
, coverStep
, loop
) where

import           Control.Applicative (Alternative(..), asum)
import           Control.Monad (ap)
import           Data.Bifunctor (first)
import           Data.Foldable (fold)
import           Data.Monoid (First(..))
import           Data.Traversable (for)
import           Facet.Name
import qualified Facet.Sequent.Class as SQ
import           Facet.Syntax ((:::)(..))
import           Fresnel.Fold
import           Fresnel.Lens
import           Fresnel.Prism (Prism', matching', prism')
import           Fresnel.Traversal (forOf, traversed)

data Pattern a
  = Wildcard
  | Var a
  | Unit
  | InL (Pattern a)
  | InR (Pattern a)
  | Pair (Pattern a) (Pattern a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative Pattern where
  pure = Var
  (<*>) = ap

instance Monad Pattern where
  m >>= f = case m of
    Wildcard -> Wildcard
    Var a    -> f a
    Unit     -> Unit
    InL p    -> InL (p >>= f)
    InR q    -> InR (q >>= f)
    Pair p q -> Pair (p >>= f) (q >>= f)


_Wildcard :: Prism' (Pattern a) ()
_Wildcard = prism' (const Wildcard) (\case
  Wildcard -> Just ()
  _        -> Nothing)

_Var :: Prism' (Pattern a) a
_Var = prism' Var (\case
  Var a -> Just a
  _     -> Nothing)

_Unit :: Prism' (Pattern a) ()
_Unit = prism' (const Unit) (\case
  Unit -> Just ()
  _    -> Nothing)

_InL :: Prism' (Pattern a) (Pattern a)
_InL = prism' InL (\case
  InL p -> Just p
  _     -> Nothing)

_InR :: Prism' (Pattern a) (Pattern a)
_InR = prism' InR (\case
  InR p -> Just p
  _     -> Nothing)

_Pair :: Prism' (Pattern a) (Pattern a, Pattern a)
_Pair = prism' (uncurry Pair) (\case
  Pair p q -> Just (p, q)
  _        -> Nothing)


data Clause a = Clause { patterns :: [Pattern Name], body :: a }

patterns_ :: Lens' (Clause a) [Pattern Name]
patterns_ = lens patterns (\ c patterns -> c{patterns})


data Type
  = Opaque
  | One
  | Type :+ Type
  | Type :* Type
  | Type :-> Type
  deriving (Eq, Ord, Show)

infixl 6 :+
infixl 7 :*
infixr 1 :->


data Branch s m a = forall x . Branch (Fold s x) (x -> m a)

(\/) :: Fold s a -> Fold s a -> Fold s a
f1 \/ f2 = getUnion (Union f1 <> Union f2)

infixr 2 \/


-- Coverage judgement

newtype Covers a = Covers { runCovers :: forall r . (r -> r -> r) -> (a -> r) -> r -> (Type -> [Pattern Name] -> r) -> r }
  deriving (Functor)

instance Applicative Covers where
  pure a = Covers (\ _ leaf _ _ -> leaf a)

  (<*>) = ap

instance Alternative Covers where
  empty = Covers (\ _ _ nil _ -> nil)

  Covers a <|> Covers b = Covers (\ (<|>) leaf nil err -> a (<|>) leaf nil err <|> b (<|>) leaf nil err)

instance Monad Covers where
  Covers m >>= k = Covers (\ fork leaf nil err -> m fork (\ a -> runCovers (k a) fork leaf nil err) nil err)

throw :: Type -> [Pattern Name] -> Covers a
throw ty ps = Covers (\ _ _ _ err -> err ty ps)

covers :: Type -> [Clause a] -> Bool
covers ty heads = runCovers (coverLoop ty heads) (&&) (const True) True (const (const False))

coverLoop :: Type -> [Clause a] -> Covers (Type, [Clause a])
coverLoop ty heads = case ty of
  hd :-> tl -> coverStep hd heads (\ prefix -> coverLoop (prefix tl))
  ty        -> pure (ty, heads) -- FIXME: fail if clauses aren't all empty

coverStep :: Type -> [Clause a] -> ((Type -> Type) -> [Clause a] -> Covers x) -> Covers x
coverStep hd heads k = case hd of
  Opaque  -> match [([], Wildcard)]                           hd heads (\ p -> [] <$ matching' _Wildcard p) k
  One     -> match [([], Unit)]                               hd heads (\ p -> [] <$ matching' _Unit p) k
  s :+ t  -> match [([s], InL Wildcard), ([t], InR Wildcard)] hd heads (\ p -> pure <$> (matching' _InL p <|> matching' _InR p)) k -- FIXME: match once and partition results
  s :* t  -> match [([s, t], Pair Wildcard Wildcard)]         hd heads (\ p -> (\ (a, b) -> [a, b]) <$> matching' _Pair p) k
  _ :-> _ -> match [([], Wildcard)]                           hd heads (\ p -> [] <$ matching' _Wildcard p) k

match :: [([Type], Pattern Name)] -> Type -> [Clause a] -> (Pattern Name -> Maybe [Pattern Name]) -> ((Type -> Type) -> [Clause a] -> Covers x) -> Covers x
match inst hd heads decompose k = do
  (prefix, canonical) <- asum (pure <$> inst)
  heads' <- forOf (traversed.patterns_) heads (\case
    p:ps | Just p' <- decompose (instantiateHead canonical p) -> pure (p' <> ps)
    ps                                                        -> throw hd ps)
  k (\ tl -> foldr (:->) tl prefix) heads'


instantiateHead :: Pattern Name -> Pattern Name -> Pattern Name
instantiateHead d Wildcard = d
instantiateHead d (Var _)  = d -- FIXME: let-bind any variables first
instantiateHead _ p        = p


loop :: (SQ.Sequent term coterm command, Applicative i) => [i term ::: Type] -> [Clause command] -> Maybe (i command)
loop ty heads = case ty of
  (_ ::: Opaque):ts -> match' (fmap (const []) . matching' _Wildcard) heads Wildcard >>= loop ts
  (_ ::: (_ :-> _)):ts -> match' (fmap (const []) . matching' _Wildcard) heads Wildcard >>= loop ts
  (_ ::: One):ts -> match' (fmap (const []) . matching' _Unit) heads Unit >>= loop ts
  (u ::: _A :* _B):ts -> do
    heads' <- forOf (traversed.patterns_) heads (\case
      p:ps | Pair p q <- instantiateHead (Pair Wildcard Wildcard) p -> Just (p:q:ps)
      _                                                             -> Nothing)
    let a wk' = SQ.µRA (\ wk k -> pure (wk (wk' u)) SQ..||. SQ.prdL1A (pure k))
        b wk' = SQ.µRA (\ wk k -> pure (wk (wk' u)) SQ..||. SQ.prdL2A (pure k))
    SQ.letA (a id) (\ wkA a -> SQ.letA (b wkA) (\ wkB b ->
      loop ((wkB a ::: _A) : (b ::: _B) : map (first (wkB . wkA)) ts) heads'))
  (u ::: _A :+ _B):ts -> do
    (headsL, headsR) <- fold <$> for heads (\case
      Clause (p:ps) b -> case instantiateHead Wildcard p of
        InL p    -> Just ([Clause (p:ps) b], [])
        InR p    -> Just ([], [Clause (p:ps) b])
        Wildcard -> Just ([Clause (Wildcard:ps) b], [Clause (Wildcard:ps) b])
        _        -> Nothing
      _    -> Nothing)
    pure u SQ..||. SQ.sumLA (SQ.µLA (\ wk a -> loop ((a ::: _A):map (first wk) ts) headsL)) (SQ.µLA (\ wk b -> loop ((b ::: _B):map (first wk) ts) headsR))
  [] | Just (Clause [] b) <- getFirst (foldMap (First . Just) heads) -> Just (pure b)
  _ -> Nothing

match' :: (Pattern Name -> Maybe [Pattern Name]) -> [Clause command] -> Pattern Name -> Maybe [Clause command]
match' decompose heads p' = forOf (traversed.patterns_) heads (\case
  p:ps | Just prefix <- decompose (instantiateHead p' p) -> Just (prefix <> ps)
  _                                                      -> Nothing)
