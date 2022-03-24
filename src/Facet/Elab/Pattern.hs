{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Elab.Pattern
( Pattern(..)
, Clause(..)
, patterns_
, Type(..)
  -- * Coverage judgement
, compilePattern
) where

import           Control.Effect.Empty
import           Control.Monad (ap)
import           Data.Bifunctor (first)
import           Data.Foldable (fold)
import           Data.Monoid (First(..))
import           Data.Traversable (for)
import           Facet.Name
import qualified Facet.Sequent.Class as SQ
import           Facet.Syntax ((:::)(..))
import           Fresnel.Fold (Fold, Union(..), preview)
import           Fresnel.Getter (to)
import           Fresnel.Lens (Lens', lens)
import           Fresnel.Prism (Prism', prism')
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


-- Coverage judgement

instantiateHead :: Pattern Name -> Pattern Name
instantiateHead (Var _) = Wildcard -- FIXME: let-bind any variables first
instantiateHead p       = p


compilePattern :: (Has Empty sig m, SQ.Sequent term coterm command, Applicative i) => [i term ::: Type] -> [Clause command] -> m (i command)
compilePattern ty heads = case ty of
  (_ ::: Opaque):ts    -> match (_Wildcard.to (const [])) heads >>= compilePattern ts
  (_ ::: (_ :-> _)):ts -> match (_Wildcard.to (const [])) heads >>= compilePattern ts
  (_ ::: One):ts       -> match (_Unit.to (const [])) heads >>= compilePattern ts
  (u ::: _A :* _B):ts -> do
    heads' <- match (getUnion (Union (_Pair.to (\ (p, q) -> [p, q])) <> Union (_Wildcard.to (const [Wildcard, Wildcard])))) heads
    let a wk' = SQ.µRA (\ wk k -> pure (wk (wk' u)) SQ..||. SQ.prdL1A (pure k))
        b wk' = SQ.µRA (\ wk k -> pure (wk (wk' u)) SQ..||. SQ.prdL2A (pure k))
    SQ.letA (a id) (\ wkA a -> SQ.letA (b wkA) (\ wkB b ->
      compilePattern ((wkB a ::: _A) : (b ::: _B) : map (first (wkB . wkA)) ts) heads'))
  (u ::: _A :+ _B):ts -> do
    (headsL, headsR) <- fold <$> for heads (\case
      Clause (p:ps) b -> case instantiateHead p of
        InL p    -> pure ([Clause (p:ps) b], [])
        InR p    -> pure ([], [Clause (p:ps) b])
        Wildcard -> pure ([Clause (Wildcard:ps) b], [Clause (Wildcard:ps) b])
        _        -> empty
      _    -> empty)
    pure u SQ..||. SQ.sumLA (SQ.µLA (\ wk a -> compilePattern ((a ::: _A):map (first wk) ts) headsL)) (SQ.µLA (\ wk b -> compilePattern ((b ::: _B):map (first wk) ts) headsR))
  [] | Just (Clause [] b) <- getFirst (foldMap (First . Just) heads) -> pure (pure b)
  _ -> empty

match :: Has Empty sig m => Fold (Pattern Name) [Pattern Name] -> [Clause command] -> m [Clause command]
match o heads = forOf (traversed.patterns_) heads (\case
  p:ps | Just prefix <- preview o (instantiateHead p) -> pure (prefix <> ps)
  _                                                   -> empty)
