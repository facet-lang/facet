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
import           Data.Traversable (for)
import           Facet.Name
import           Facet.Quote
import qualified Facet.Sequent.Class as C
import qualified Facet.Sequent.Expr as X
import           Facet.Sequent.Pattern
import           Facet.Sequent.Type
import           Fresnel.Fold (Fold, Union(..), folded, preview)
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


compileClauses :: Has Empty sig m => [X.Term] -> Type -> [Clause X.Term] -> QuoterT m X.Term
compileClauses ctx (_A :-> _T) heads = C.lamR (compileClausesBody ctx _A _T heads)
compileClauses _ _T heads
  | Just (Clause [] b) <- preview folded heads = pure b
  | otherwise                                  = empty

compileClausesBody :: Has Empty sig m => [X.Term] -> Type -> Type -> [Clause X.Term] -> QuoterT m X.Term -> QuoterT m X.Coterm -> QuoterT m X.Command
compileClausesBody ctx _A _T heads v k = case _A of
  Opaque   -> (match (_Var._Nothing.to (const [])) heads >>= compileClauses ctx _T) C..|. k
  _ :-> _  -> (match (_Var._Nothing.to (const [])) heads >>= compileClauses ctx _T) C..|. k
  One      -> (match (_Unit.to (const [])) heads >>= compileClauses ctx _T) C..|. k
  _A :* _B -> match (getUnion (Union (_Pair.to (\ (p, q) -> [p, q])) <> Union (_Var._Nothing.to (const [Var Nothing, Var Nothing])))) heads >>= \ heads' ->
    C.let' (C.µR (\ k -> v C..|. C.prdL1 k)) (\ _ ->
    C.let' (C.µR (\ k -> v C..|. C.prdL2 k)) (\ _ ->
      compileClauses ctx _T heads' C..|. k))
  _A :+ _B -> do
    heads' <- fold <$> for heads (\case
      Clause (p:ps) b -> case instantiateHead p of
        InL p       -> pure (singleton 0 [Clause (p:ps) b])
        InR p       -> pure (singleton 1 [Clause (p:ps) b])
        Var Nothing -> pure (fromList [[Clause (Var Nothing:ps) b], [Clause (Var Nothing:ps) b]])
        _           -> empty
      _    -> empty)
    v C..|. C.sumL
      [ C.µL (\ v -> compileClausesBody ctx _A _T (heads' `at` 0) v k)
      , C.µL (\ v -> compileClausesBody ctx _B _T (heads' `at` 1) v k) ]


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
