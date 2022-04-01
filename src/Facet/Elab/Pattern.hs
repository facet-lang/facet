module Facet.Elab.Pattern
( Clause(..)
, patterns_
  -- * Coverage judgement
, compileClauses
, Column(..)
, RowIndex
, singleton
, fromList
, at
) where

import           Control.Effect.Empty
import           Data.Foldable (fold)
import qualified Data.IntMap as IntMap
import           Data.Monoid (First(..))
import           Data.Traversable (for)
import           Facet.Name
import qualified Facet.Sequent.Expr as X
import           Facet.Sequent.Pattern
import           Facet.Sequent.Type
import           Facet.Syntax (Var(..))
import           Fresnel.Fold (Fold, Union(..), preview)
import           Fresnel.Getter (to)
import           Fresnel.Lens (Lens', lens)
import           Fresnel.Maybe (_Nothing)
import           Fresnel.Traversal (forOf, traversed)

data Clause a = Clause { patterns :: [Pattern Name], body :: a }

patterns_ :: Lens' (Clause a) [Pattern Name]
patterns_ = lens patterns (\ c patterns -> c{patterns})


-- Coverage judgement

instantiateHead :: Pattern Name -> Pattern Name
instantiateHead (Var (Just _)) = Var Nothing -- FIXME: let-bind any variables first
instantiateHead p              = p


compileClauses :: Has Empty sig m => GName -> [X.Term] -> Type -> [Clause X.Term] -> m X.Term
compileClauses root ctx (_A :-> _T) heads = X.lamRA $ case _A of
  -- FIXME: look variables up in @ctx@ instead of hard-coding de Bruijn indices
  Opaque   -> (match (_Var._Nothing.to (const [])) heads >>= compileClauses root ctx _T) X..||. X.covarA (Free 0)
  _ :-> _  -> (match (_Var._Nothing.to (const [])) heads >>= compileClauses root ctx _T) X..||. X.covarA (Free 0)
  One      -> (match (_Unit.to (const [])) heads >>= compileClauses root ctx _T) X..||. X.covarA (Free 0)
  _A :* _B -> match (getUnion (Union (_Pair.to (\ (p, q) -> [p, q])) <> Union (_Var._Nothing.to (const [Var Nothing, Var Nothing])))) heads >>= \ heads' ->
    X.letA (X.µRA (X.varA (Free 2) X..||. X.prdL1A (X.covarA (Free 0)))) (
    X.letA (X.µRA (X.varA (Free 3) X..||. X.prdL2A (X.covarA (Free 0)))) (
      compileClauses root ctx _T heads' X..||. X.covarA (Free 2)))
  _A :+ _B -> do
    heads' <- fold <$> for heads (\case
      Clause (p:ps) b -> case instantiateHead p of
        InL p       -> pure (singleton 0 [Clause (p:ps) b])
        InR p       -> pure (singleton 1 [Clause (p:ps) b])
        Var Nothing -> pure (fromList [[Clause (Var Nothing:ps) b], [Clause (Var Nothing:ps) b]])
        _           -> empty
      _    -> empty)
    X.varA (Free 1) X..||. X.sumLA
      -- FIXME: n-ary sums
      -- FIXME: don't create extra lambdas for the recursive calls
      (X.µLA (compileClauses root ctx (_A :-> _T) (heads' `at` 0) X..||. X.covarA (Free 0)))
      (X.µLA (compileClauses root ctx (_B :-> _T) (heads' `at` 1) X..||. X.covarA (Free 0)))
compileClauses _ _ _T heads
  | Just (Clause [] b) <- getFirst (foldMap (First . Just) heads) = pure b
  | otherwise                                                     = empty

match :: Has Empty sig m => Fold (Pattern Name) [Pattern Name] -> [Clause X.Term] -> m [Clause X.Term]
match o heads = forOf (traversed.patterns_) heads (\case
  p:ps | Just prefix <- preview o (instantiateHead p) -> pure (prefix <> ps)
  _                                                   -> empty)


newtype Column a = Column { getColumn :: IntMap.IntMap a }

instance Semigroup a => Semigroup (Column a) where
  as <> bs = Column (IntMap.unionWith (<>) (getColumn as) (getColumn bs))

instance Monoid a => Monoid (Column a) where
  mempty = Column mempty

type RowIndex = Int

-- | Construct a sparse 'Column' from a single value.
singleton :: RowIndex -> a -> Column a
singleton row a = Column (IntMap.singleton row a)

-- | Construct a dense 'Column' from a list of values.
fromList :: [a] -> Column a
fromList = Column . IntMap.fromList . zipWith (\ a b -> (a, b)) [0..]

at :: Column a -> RowIndex -> a
at (Column m) i = m IntMap.! i
