module Facet.Sequent.Expr
( -- * Terms
  Term(..)
  -- * Coterms
, Coterm(..)
  -- * Commands
, Command(..)
  -- * Scopes
, Scope
, abstractLR
, instantiateLR
) where

import Data.Text (Text)
import Facet.Name
import Facet.Snoc
import Facet.Snoc.NonEmpty
import Facet.Syntax
import Fresnel.Lens (Lens', lens)

-- Terms

data Term
  = Var (Var Index)
  | MuR Command
  | LamR Command
  | SumR Int Term
  | BottomR Command
  | UnitR
  | PrdR Term Term
  | StringR Text


-- Coterms

data Coterm
  = Covar (Var Index)
  | MuL Command
  | LamL Term Coterm
  | SumL [Coterm]
  | UnitL
  | PrdL1 Coterm
  | PrdL2 Coterm


-- Commands

data Command
  = Term :|: Coterm
  | Let Term Command


-- Scopes

newtype Scope = Scope { getScope :: Command }

abstractLR :: Name -> Name -> (Command -> Scope)
abstractLR t c = Scope . replaceCommand (0, freeL, boundL) (0, freeR, boundR) where
  freeR outer name
    | name == t = Var (Bound outer)
    | otherwise = Var (Free (Nil:|>name))
  freeL outer name
    | name == c = Covar (Bound outer)
    | otherwise = Covar (Free (Nil:|>name))
  boundR _ inner = Var (Bound inner)
  boundL _ inner = Covar (Bound inner)

instantiateLR :: Term -> Coterm -> (Scope -> Command)
instantiateLR t c = replaceCommand (0, freeL, boundL) (0, freeR, boundR) . getScope where
  freeR _ name = Var   (Free (Nil:|>name))
  freeL _ name = Covar (Free (Nil:|>name))
  boundR outer inner
    | outer == inner = t
    | otherwise      = Var (Bound inner)
  boundL outer inner
    | outer == inner = c
    | otherwise      = Covar (Bound inner)

data Replacer t = Replacer
  { outer :: Index
  , free  :: Index -> Name -> t
  , bound :: Index -> Index -> t
  }

outer_ :: Lens' (Replacer t) Index
outer_ = lens outer (\ Replacer{ free, bound } outer -> Replacer{ outer, free, bound })

free' :: Replacer t -> Name -> t
free' Replacer{ outer, free } = free outer

bound' :: Replacer t -> Index -> t
bound' Replacer{ outer, bound } = bound outer

replaceTerm :: (Index, Index -> Name -> Coterm, Index -> Index -> Coterm) -> (Index, Index -> Name -> Term, Index -> Index -> Term) -> (Term -> Term)
replaceTerm (outerL, freeL, boundL) (outerR, freeR, boundR) within = case within of
  Var (Free (Nil:|>n)) -> freeR outerR n
  Var (Free _)         -> within
  Var (Bound inner)    -> boundR outerR inner
  MuR b                -> MuR (replaceCommand (succ outerL, freeL, boundL) (outerR, freeR, boundR) b)
  LamR b               -> LamR (replaceCommand (succ outerL, freeL, boundL) (succ outerR, freeR, boundR) b)
  SumR i a             -> SumR i (replaceTerm (outerL, freeL, boundL) (outerR, freeR, boundR) a)
  BottomR b            -> BottomR (replaceCommand (outerL, freeL, boundL) (outerR, freeR, boundR) b)
  UnitR                -> within
  PrdR a b             -> PrdR (replaceTerm (outerL, freeL, boundL) (outerR, freeR, boundR) a) (replaceTerm (outerL, freeL, boundL) (outerR, freeR, boundR) b)
  StringR _            -> within

replaceCoterm :: (Index, Index -> Name -> Coterm, Index -> Index -> Coterm) -> (Index, Index -> Name -> Term, Index -> Index -> Term) -> (Coterm -> Coterm)
replaceCoterm (outerL, freeL, boundL) (outerR, freeR, boundR) within = case within of
  Covar (Free (Nil:|>n)) -> freeL outerL n
  Covar (Free _)         -> within
  Covar (Bound inner)    -> boundL outerL inner
  MuL b                  -> MuL (replaceCommand (outerL, freeL, boundL) (succ outerR, freeR, boundR) b)
  LamL a k               -> LamL (replaceTerm (outerL, freeL, boundL) (outerR, freeR, boundR) a) (replaceCoterm (outerL, freeL, boundL) (outerR, freeR, boundR) k)
  SumL cs                -> SumL (map (replaceCoterm (outerL, freeL, boundL) (outerR, freeR, boundR)) cs)
  UnitL                  -> within
  PrdL1 k                -> PrdL1 (replaceCoterm (outerL, freeL, boundL) (outerR, freeR, boundR) k)
  PrdL2 k                -> PrdL2 (replaceCoterm (outerL, freeL, boundL) (outerR, freeR, boundR) k)

replaceCommand :: (Index, Index -> Name -> Coterm, Index -> Index -> Coterm) -> (Index, Index -> Name -> Term, Index -> Index -> Term) -> (Command -> Command)
replaceCommand (outerL, freeL, boundL) (outerR, freeR, boundR) = \case
  t :|: c -> replaceTerm (outerL, freeL, boundL) (outerR, freeR, boundR) t :|: replaceCoterm (outerL, freeL, boundL) (outerR, freeR, boundR) c
  Let t b -> Let (replaceTerm (outerL, freeL, boundL) (outerR, freeR, boundR) t) (replaceCommand (outerL, freeL, boundL) (succ outerR, freeR, boundR) b)
