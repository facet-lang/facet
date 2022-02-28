{-# LANGUAGE ExistentialQuantification #-}
module Facet.Elab.Pattern
( Pattern(..)
, Clause(..)
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
import Fresnel.Effect
import Fresnel.Fold
import Fresnel.Iso
import Fresnel.Lens
import Fresnel.List (head_)
import Fresnel.Traversal (traversed)

data Pattern
  = Wildcard
  | Var Name
  | Unit
  | Pair Pattern Pattern

newtype Clause = Clause [Pattern]

patterns_ :: Iso' Clause [Pattern]
patterns_ = coerced


data Type
  = String
  | ForAll
  | Arrow
  | Zero
  | One
  | Type :+ Type
  | Type :* Type
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
    Wildcard -> modify advance
    Var _    -> modify advance
    _        -> empty)
  Just ForAll{} -> use heads_ >>= foldMapByOf (folded.patterns_.head_) (<|>) empty (\case
    Wildcard -> modify advance
    Var _    -> modify advance
    _        -> empty)
  Just Arrow{}  -> use heads_ >>= foldMapByOf (folded.patterns_.head_) (<|>) empty (\case
    Wildcard -> modify advance
    Var _    -> modify advance
    _        -> empty)
  Just Zero     -> use heads_ >>= foldMapByOf (folded.patterns_.head_) (<|>) empty (\case
    Wildcard -> modify advance
    Var _    -> modify advance
    _        -> empty)
  Just One{}    -> use heads_ >>= foldMapByOf (folded.patterns_.head_) (<|>) empty (\case
    Wildcard -> modify advance
    Var _    -> modify advance
    Unit     -> modify advance
    _        -> empty)
  Just (t1 :* t2) -> use heads_ >>= foldMapByOf (folded.patterns_.head_) (<|>) empty (\case
    Wildcard   -> context_ %= (\ ctx -> t1:t2:ctx) >> heads_.traversed.patterns_ %= (\ clause -> Wildcard:Wildcard:clause)
    -- FIXME: this should bind fresh names
    Var n      -> context_ %= (\ ctx -> t1:t2:ctx) >> heads_.traversed.patterns_ %= (\ clause -> Var n:Var n:clause)
    Pair p1 p2 -> context_ %= (\ ctx -> t1:t2:ctx) >> heads_.traversed.patterns_ %= (\ clause -> p1:p2:clause)
    _          -> empty)
  Just Comp{}   -> empty
  _            -> empty
