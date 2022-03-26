{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Elab.Pattern
( Clause(..)
, patterns_
  -- * Coverage judgement
, compilePattern
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
    pure u SQ..||. SQ.sumLA
      (SQ.µLA (\ wk a -> compilePattern ((a ::: _A):map (first wk) ts) headsL))
      (SQ.µLA (\ wk b -> compilePattern ((b ::: _B):map (first wk) ts) headsR))
  [] | Just (Clause [] b) <- getFirst (foldMap (First . Just) heads) -> pure (pure b)
  _ -> empty

match :: Has Empty sig m => Fold (Pattern Name) [Pattern Name] -> [Clause command] -> m [Clause command]
match o heads = forOf (traversed.patterns_) heads (\case
  p:ps | Just prefix <- preview o (instantiateHead p) -> pure (prefix <> ps)
  _                                                   -> empty)
