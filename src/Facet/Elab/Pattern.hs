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
import Facet.Pattern
import Facet.Type.Norm (Type)
import Fresnel.Effect
import Fresnel.Fold
import Fresnel.Iso

newtype Clause a = Clause [Pattern a]

patterns_ :: Iso (Clause a) (Clause b) [Pattern a] [Pattern b]
patterns_ = coerced

newtype Tableau a = Tableau [Clause a]

clauses_ :: Iso' (Tableau a) [Clause a]
clauses_ = coerced


data Branch s m a = forall x . Branch (Fold s x) (x -> m a)

(\/) :: Fold s a -> Fold s a -> Fold s a
f1 \/ f2 = getUnion (Union f1 <> Union f2)

infixr 2 \/


-- Coverage judgement

newtype Covers m a = Covers { covers :: StateC [Type] m a }
  deriving (Algebra (State [Type] :+: sig), Applicative, Functor, Monad)


coverOne :: Has Empty sig m => Covers m ()
coverOne = use context_ >>= \case
  []    -> empty
  _:ctx -> context_ .= ctx

context_ :: Iso' [Type] [Type]
context_ = iso id id
