{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Elab.Pattern
( Clause(..)
, patterns_
  -- * Coverage judgement
, compileClauses
) where

import           Control.Effect.Empty
import           Data.Bifunctor (first)
import           Data.Foldable (fold)
import           Data.Monoid (First(..))
import           Data.Traversable (for)
import           Facet.Name
import qualified Facet.Sequent.Class as SQ
import           Facet.Sequent.Pattern
import           Facet.Sequent.Type
import           Facet.Syntax ((:::)(..))
import           Fresnel.Fold (Fold, Union(..), preview)
import           Fresnel.Getter (to)
import           Fresnel.Lens (Lens', lens)
import           Fresnel.Traversal (forOf, traversed)

data Clause a = Clause { patterns :: [Pattern Name], body :: a }

patterns_ :: Lens' (Clause a) [Pattern Name]
patterns_ = lens patterns (\ c patterns -> c{patterns})


-- Coverage judgement

instantiateHead :: Pattern Name -> Pattern Name
instantiateHead (Var _) = Wildcard -- FIXME: let-bind any variables first
instantiateHead p       = p


compileClauses :: (Has Empty sig m, SQ.Sequent term coterm command, Applicative i) => [i term ::: Type] -> [Clause term] -> m (i term)
compileClauses (ty:ts) heads = SQ.lamRA $ \ wk _v k -> case ty of
  (_ ::: Opaque)    -> (match (_Wildcard.to (const [])) heads >>= compileClauses (map (first wk) ts)) SQ..||. pure k
  (_ ::: (_ :-> _)) -> (match (_Wildcard.to (const [])) heads >>= compileClauses (map (first wk) ts)) SQ..||. pure k
  (_ ::: One)       -> (match (_Unit.to (const [])) heads >>= compileClauses (map (first wk) ts)) SQ..||. pure k
  (u ::: _A :* _B) -> do
    heads' <- match (getUnion (Union (_Pair.to (\ (p, q) -> [p, q])) <> Union (_Wildcard.to (const [Wildcard, Wildcard])))) heads
    let a wk' = SQ.µRA (\ wk k -> pure (wk (wk' u)) SQ..||. SQ.prdL1A (pure k))
        b wk' = SQ.µRA (\ wk k -> pure (wk (wk' u)) SQ..||. SQ.prdL2A (pure k))
    SQ.letA (a wk) (\ wkA a -> SQ.letA (b (wkA . wk)) (\ wkB b ->
      compileClauses ((wkB a ::: _A) : (b ::: _B) : map (first (wkB . wkA . wk)) ts) heads' SQ..||. pure (wkB (wkA k))))
  (u ::: _A :+ _B) -> do
    (headsL, headsR) <- fold <$> for heads (\case
      Clause (p:ps) b -> case instantiateHead p of
        InL p    -> pure ([Clause (p:ps) b], [])
        InR p    -> pure ([], [Clause (p:ps) b])
        Wildcard -> pure ([Clause (Wildcard:ps) b], [Clause (Wildcard:ps) b])
        _        -> empty
      _    -> empty)
    pure (wk u) SQ..||. SQ.sumLA
      (SQ.µLA (\ wk' a -> compileClauses ((a ::: _A):map (first (wk' . wk)) ts) headsL SQ..||. pure (wk' k)))
      (SQ.µLA (\ wk' b -> compileClauses ((b ::: _B):map (first (wk' . wk)) ts) headsR SQ..||. pure (wk' k)))
compileClauses [] heads
  | Just (Clause [] b) <- getFirst (foldMap (First . Just) heads) = pure (pure b)
  | otherwise                                                     = empty

match :: Has Empty sig m => Fold (Pattern Name) [Pattern Name] -> [Clause command] -> m [Clause command]
match o heads = forOf (traversed.patterns_) heads (\case
  p:ps | Just prefix <- preview o (instantiateHead p) -> pure (prefix <> ps)
  _                                                   -> empty)
