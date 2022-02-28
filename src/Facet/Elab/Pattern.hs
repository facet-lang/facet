{-# LANGUAGE ExistentialQuantification #-}
module Facet.Elab.Pattern
( Clause(..)
, patterns_
, Type(..)
, Tableau(..)
, heads_
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
import Facet.Interface
import Facet.Name
import Facet.Pattern
import Fresnel.Effect
import Fresnel.Fold
import Fresnel.Iso
import Fresnel.Lens
import Fresnel.List (head_)

newtype Clause = Clause [Pattern Name]

patterns_ :: Iso' Clause [Pattern Name]
patterns_ = coerced


data Type
  = String
  | ForAll
  | Arrow
  | Sum [Type]
  | Prd [Type]
  | Comp (Signature Type)


data Tableau = Tableau
  { context :: [Type]
  , heads   :: [Clause]
  }

heads_ :: Lens' Tableau [Clause]
heads_ = lens heads (\ t heads -> t{heads})

context_ :: Lens' Tableau [Type]
context_ = lens context (\ t context -> t{context})

advance :: Tableau -> Tableau
advance Tableau{ context, heads } = Tableau (tail context) (tail heads)


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
  Just String   -> use heads_ >>= foldMapByOf (folded.patterns_.head_) (<|>) empty (\case
    PWildcard -> modify advance
    PVar _    -> modify advance
    _         -> empty)
  Just ForAll{} -> use heads_ >>= foldMapByOf (folded.patterns_.head_) (<|>) empty (\case
    PWildcard -> modify advance
    PVar _    -> modify advance
    _         -> empty)
  Just Arrow{}  -> use heads_ >>= foldMapByOf (folded.patterns_.head_) (<|>) empty (\case
    PWildcard -> modify advance
    PVar _    -> modify advance
    _         -> empty)
  Just (Prd []) -> use heads_ >>= foldMapByOf (folded.patterns_.head_) (<|>) empty (\case
    PWildcard -> modify advance
    PVar _    -> modify advance
    _         -> empty)
  Just Comp{}   -> empty
  _            -> empty
