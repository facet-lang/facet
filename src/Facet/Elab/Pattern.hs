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
import Fresnel.Effect hiding (view)
import Fresnel.Fold
import Fresnel.Iso
import Fresnel.Lens
import Fresnel.List (head_)
import Fresnel.Traversal (traversed)

data Pattern
  = Wildcard
  | Var Name
  | Unit
  | InL Pattern
  | InR Pattern
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
coverStep = use context_ >>= \case
  String:ctx   -> use heads_ >>= traverseOf_ (folded.patterns_.head_) (\case
    Wildcard -> pure ()
    Var _    -> pure ()
    _        -> empty) >> context_ .= ctx >> heads_.traversed.patterns_ %= tail
  ForAll{}:ctx -> use heads_ >>= traverseOf_ (folded.patterns_.head_) (\case
    Wildcard -> pure ()
    Var _    -> pure ()
    _        -> empty) >> context_ .= ctx >> heads_.traversed.patterns_ %= tail
  Arrow{}:ctx  -> use heads_ >>= traverseOf_ (folded.patterns_.head_) (\case
    Wildcard -> pure ()
    Var _    -> pure ()
    _        -> empty) >> context_ .= ctx >> heads_.traversed.patterns_ %= tail
  Zero:ctx     -> use heads_ >>= traverseOf_ (folded.patterns_.head_) (\case
    Wildcard -> pure ()
    Var _    -> pure ()
    _        -> empty) >> context_ .= ctx >> heads_.traversed.patterns_ %= tail
  One:ctx      -> use heads_ >>= traverseOf_ (folded.patterns_.head_) (\case
    Wildcard -> pure ()
    Var _    -> pure ()
    Unit     -> pure ()
    _        -> empty) >> context_ .= ctx >> heads_.traversed.patterns_ %= tail
  (t1 :+ t2):ctx -> uses heads_ (foldMapOf (folded.patterns_) (\case
      Wildcard:ps -> Just ([Clause (Wildcard:ps)], [Clause (Wildcard:ps)])
      Var n:ps    -> Just ([Clause (Var n:ps)],    [Clause (Var n:ps)])
      InL p:ps    -> Just ([Clause (p:ps)],        [Clause []])
      InR q:qs    -> Just ([Clause []],            [Clause (q:qs)])
      _           -> Nothing))
    >>= \case
      Just (cs1, cs2) -> put (Tableau (t1:ctx) cs1) <|> put (Tableau (t2:ctx) cs2)
      Nothing         -> empty
  (t1 :* t2):ctx -> use heads_ >>= foldMapByOf (folded.patterns_.head_) (<|>) empty (\case
    Wildcard   -> context_ .= t1:t2:ctx >> heads_.traversed.patterns_ %= (\ clause -> Wildcard:Wildcard:clause)
    -- FIXME: this should bind fresh names
    Var n      -> context_ .= t1:t2:ctx >> heads_.traversed.patterns_ %= (\ clause -> Var n:Var n:clause)
    Pair p1 p2 -> context_ .= t1:t2:ctx >> heads_.traversed.patterns_ %= (\ clause -> p1:p2:clause)
    _          -> empty)
  Comp{}:_     -> empty
  []           -> pure () -- FIXME: fail if clauses aren't all empty
