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
import           Facet.Syntax (type (~>))
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


compileClauses :: (Has Empty sig m, SQ.Sequent term coterm command, Applicative i) => Ctx i term -> Type -> [Clause term] -> m (i term)
compileClauses ctx (_A :-> _T) heads = SQ.lamRA $ \ wk v k -> case _A of
  Opaque   -> (match (_Var._Nothing.to (const [])) heads >>= compileClauses (skip ctx wk) _T) SQ..||. pure k
  _ :-> _  -> (match (_Var._Nothing.to (const [])) heads >>= compileClauses (skip ctx wk) _T) SQ..||. pure k
  One      -> (match (_Unit.to (const [])) heads >>= compileClauses (skip ctx wk) _T) SQ..||. pure k
  _A :* _B -> match (getUnion (Union (_Pair.to (\ (p, q) -> [p, q])) <> Union (_Var._Nothing.to (const [Var Nothing, Var Nothing])))) heads >>= \ heads' ->
    SQ.letA (SQ.µRA (\ wk k -> pure (wk v)       SQ..||. SQ.prdL1A (pure k))) (\ wkA _ ->
    SQ.letA (SQ.µRA (\ wk k -> pure (wk (wkA v)) SQ..||. SQ.prdL2A (pure k))) (\ wkB _ ->
      compileClauses (skip ctx (wkB . wkA . wk)) _T heads' SQ..||. pure (wkB (wkA k))))
  _A :+ _B -> do
    (headsL, headsR) <- fold <$> for heads (\case
      Clause (p:ps) b -> case instantiateHead p of
        InL p       -> pure ([Clause (p:ps) b], [])
        InR p       -> pure ([], [Clause (p:ps) b])
        Var Nothing -> pure ([Clause (Var Nothing:ps) b], [Clause (Var Nothing:ps) b])
        _           -> empty
      _    -> empty)
    pure v SQ..||. SQ.sumLA
      (SQ.µLA (\ wk2 _ -> compileClauses (skip ctx (wk2 . wk)) _T headsL SQ..||. pure (wk2 k)))
      (SQ.µLA (\ wk2 _ -> compileClauses (skip ctx (wk2 . wk)) _T headsR SQ..||. pure (wk2 k)))
compileClauses _ _T heads
  | Just (Clause [] b) <- getFirst (foldMap (First . Just) heads) = pure (pure b)
  | otherwise                                                     = empty

match :: Has Empty sig m => Fold (Pattern Name) [Pattern Name] -> [Clause command] -> m [Clause command]
match o heads = forOf (traversed.patterns_) heads (\case
  p:ps | Just prefix <- preview o (instantiateHead p) -> pure (prefix <> ps)
  _                                                   -> empty)


data Ctx j t
  = Nil
  | forall i . Bind (Ctx i t) (i ~> j) Type (j t)

skip :: Ctx i t -> (i ~> j) -> Ctx j t
skip Nil _                    = Nil
skip (Bind ctx wk1 ty tm) wk2 = Bind ctx (wk2 . wk1) ty (wk2 tm)
