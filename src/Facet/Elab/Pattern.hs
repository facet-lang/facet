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
) where

import Control.Algebra
import Control.Carrier.State.Church
import Control.Effect.Empty
import Facet.Name
import Facet.Pattern
import Facet.Type.Norm (Type)
import Fresnel.Effect
import Fresnel.Fold
import Fresnel.Iso
import Fresnel.Lens

newtype Clause = Clause [Pattern Name]

patterns_ :: Iso' Clause [Pattern Name]
patterns_ = coerced

data Tableau = Tableau
  { context :: [Type]
  , clauses :: [Clause]
  }

clauses_ :: Lens' Tableau [Clause]
clauses_ = lens (\ (Tableau _ clauses) -> clauses) (\ (Tableau context _) clauses -> Tableau context clauses)

context_ :: Lens' Tableau [Type]
context_ = lens (\ (Tableau context _) -> context) (\ (Tableau _ clauses) context -> Tableau context clauses)


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
