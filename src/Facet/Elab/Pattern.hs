{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Elab.Pattern
( Clause(..)
, patterns_
  -- * Coverage judgement
, compileClauses
) where

import           Control.Effect.Empty
import           Data.Foldable (fold)
import           Data.Monoid (First(..))
import           Data.Traversable (for)
import           Facet.Name
import qualified Facet.Sequent.Class as SQ
import           Facet.Sequent.Pattern
import           Facet.Sequent.Type
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


compileClauses :: (Has Empty sig m, SQ.Sequent term coterm command, Applicative i) => [Type] -> [Clause term] -> m (i term)
compileClauses (ty:ts) heads = SQ.lamRA $ \ _wk v k -> case ty of
  Opaque    -> (match (_Wildcard.to (const [])) heads >>= compileClauses ts) SQ..||. pure k
  _ :-> _   -> (match (_Wildcard.to (const [])) heads >>= compileClauses ts) SQ..||. pure k
  One       -> (match (_Unit.to (const [])) heads >>= compileClauses ts) SQ..||. pure k
  _A :* _B  -> match (getUnion (Union (_Pair.to (\ (p, q) -> [p, q])) <> Union (_Wildcard.to (const [Wildcard, Wildcard])))) heads >>= \ heads' ->
    SQ.letA (SQ.µRA (\ wk k -> pure (wk v)       SQ..||. SQ.prdL1A (pure k))) (\ wkA _ ->
    SQ.letA (SQ.µRA (\ wk k -> pure (wk (wkA v)) SQ..||. SQ.prdL2A (pure k))) (\ wkB _ ->
      compileClauses (_A:_B:ts) heads' SQ..||. pure (wkB (wkA k))))
  _A :+ _B  -> do
    (headsL, headsR) <- fold <$> for heads (\case
      Clause (p:ps) b -> case instantiateHead p of
        InL p    -> pure ([Clause (p:ps) b], [])
        InR p    -> pure ([], [Clause (p:ps) b])
        Wildcard -> pure ([Clause (Wildcard:ps) b], [Clause (Wildcard:ps) b])
        _        -> empty
      _    -> empty)
    pure v SQ..||. SQ.sumLA
      (SQ.µLA (\ wk _ -> compileClauses (_A:ts) headsL SQ..||. pure (wk k)))
      (SQ.µLA (\ wk _ -> compileClauses (_B:ts) headsR SQ..||. pure (wk k)))
compileClauses [] heads
  | Just (Clause [] b) <- getFirst (foldMap (First . Just) heads) = pure (pure b)
  | otherwise                                                     = empty

match :: Has Empty sig m => Fold (Pattern Name) [Pattern Name] -> [Clause command] -> m [Clause command]
match o heads = forOf (traversed.patterns_) heads (\case
  p:ps | Just prefix <- preview o (instantiateHead p) -> pure (prefix <> ps)
  _                                                   -> empty)
