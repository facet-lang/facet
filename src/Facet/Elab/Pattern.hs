{-# LANGUAGE ExistentialQuantification #-}
module Facet.Elab.Pattern
( Clause(..)
, patterns_
, Tableau(..)
, clauses_
, Branch(..)
, (\/)
  -- * Coverage judgement
, Covers(..)
, coverOne
, coverStep
) where

import Control.Algebra
import Control.Carrier.State.Church
import Control.Effect.Choose
import Control.Effect.Empty
import Control.Effect.NonDet (NonDet)
import Facet.Name
import Facet.Pattern
import Facet.Type.Norm as T (Type(..))
import Fresnel.Effect
import Fresnel.Fold
import Fresnel.Iso
import Fresnel.Lens
import Fresnel.List (head_)
import Fresnel.Traversal (traversed)

newtype Clause = Clause [Pattern Name]

patterns_ :: Iso' Clause [Pattern Name]
patterns_ = coerced

data Tableau = Tableau
  { context :: [Type]
  , clauses :: [Clause]
  }

clauses_ :: Lens' Tableau [Clause]
clauses_ = lens clauses (\ t clauses -> t{clauses})

context_ :: Lens' Tableau [Type]
context_ = lens context (\ t context -> t{context})


data Branch s m a = forall x . Branch (Fold s x) (x -> m a)

(\/) :: Fold s a -> Fold s a -> Fold s a
f1 \/ f2 = getUnion (Union f1 <> Union f2)

infixr 2 \/


-- Coverage judgement

newtype Covers m a = Covers { covers :: StateC Tableau m a }
  deriving (Algebra (State Tableau :+: sig), Applicative, Functor, Monad)


coverOne :: Has Empty sig m => Covers m ()
coverOne = use context_ >>= \case
  []    -> empty
  _:ctx -> context_ .= ctx

coverStep :: Has NonDet sig m => Covers m ()
coverStep = uses context_ (preview head_) >>= \case
  Just T.String -> use clauses_ >>= foldMapByOf (folded.patterns_.head_) (<|>) empty (\case
    PWildcard -> context_ %= tail >> clauses_.traversed.patterns_ %= tail
    PVar _    -> context_ %= tail >> clauses_.traversed.patterns_ %= tail
    _         -> empty)
  Just T.ForAll{} -> use clauses_ >>= foldMapByOf (folded.patterns_.head_) (<|>) empty (\case
    PWildcard -> context_ %= tail >> clauses_.traversed.patterns_ %= tail
    PVar _    -> context_ %= tail >> clauses_.traversed.patterns_ %= tail
    _         -> empty)
  _            -> empty
