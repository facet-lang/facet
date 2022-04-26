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
abstractLR t c = Scope . replace (freeR, boundR) (freeL, boundL) where
  freeR outer name
    | name == t = Var (Bound outer)
    | otherwise = Var (Free (Nil:|>name))
  freeL outer name
    | name == c = Covar (Bound outer)
    | otherwise = Covar (Free (Nil:|>name))
  boundR _ inner = Var (Bound inner)
  boundL _ inner = Covar (Bound inner)

instantiateLR :: Term -> Coterm -> (Scope -> Command)
instantiateLR t c = replace (freeR, boundR) (freeL, boundL) . getScope where
  freeR _ name = Var   (Free (Nil:|>name))
  freeL _ name = Covar (Free (Nil:|>name))
  boundR outer inner
    | outer == inner = t
    | otherwise      = Var (Bound inner)
  boundL outer inner
    | outer == inner = c
    | otherwise      = Covar (Bound inner)

replaceTerm :: (Index, Index -> Name -> Term, Index -> Index -> Term) -> (Index, Index -> Name -> Coterm, Index -> Index -> Coterm) -> (Term -> Term)
replaceTerm (outerR, freeR, boundR) (outerL, freeL, boundL) within = case within of
  Var (Free (Nil:|>n)) -> freeR outerR n
  Var (Free _)         -> within
  Var (Bound inner)    -> boundR outerR inner
  MuR b                -> MuR (replaceCommand (outerR, freeR, boundR) (succ outerL, freeL, boundL) b)
  LamR b               -> LamR (replaceCommand (succ outerR, freeR, boundR) (succ outerL, freeL, boundL) b)
  SumR i a             -> SumR i (replaceTerm (outerR, freeR, boundR) (outerL, freeL, boundL) a)
  BottomR b            -> BottomR (replaceCommand (outerR, freeR, boundR) (outerL, freeL, boundL) b)
  UnitR                -> within
  PrdR a b             -> PrdR (replaceTerm (outerR, freeR, boundR) (outerL, freeL, boundL) a) (replaceTerm (outerR, freeR, boundR) (outerL, freeL, boundL) b)
  StringR _            -> within

replaceCoterm :: (Index, Index -> Name -> Term, Index -> Index -> Term) -> (Index, Index -> Name -> Coterm, Index -> Index -> Coterm) -> (Coterm -> Coterm)
replaceCoterm (outerR, freeR, boundR) (outerL, freeL, boundL) within = case within of
  Covar (Free (Nil:|>n)) -> freeL outerL n
  Covar (Free _)         -> within
  Covar (Bound inner)    -> boundL outerL inner
  MuL b                  -> MuL (replaceCommand (succ outerR, freeR, boundR) (outerL, freeL, boundL) b)
  LamL a k               -> LamL (replaceTerm (outerR, freeR, boundR) (outerL, freeL, boundL) a) (replaceCoterm (outerR, freeR, boundR) (outerL, freeL, boundL) k)
  SumL cs                -> SumL (map (replaceCoterm (outerR, freeR, boundR) (outerL, freeL, boundL)) cs)
  UnitL                  -> within
  PrdL1 k                -> PrdL1 (replaceCoterm (outerR, freeR, boundR) (outerL, freeL, boundL) k)
  PrdL2 k                -> PrdL2 (replaceCoterm (outerR, freeR, boundR) (outerL, freeL, boundL) k)

replaceCommand :: (Index, Index -> Name -> Term, Index -> Index -> Term) -> (Index, Index -> Name -> Coterm, Index -> Index -> Coterm) -> (Command -> Command)
replaceCommand (outerR, freeR, boundR) (outerL, freeL, boundL) = \case
  t :|: c -> replaceTerm (outerR, freeR, boundR) (outerL, freeL, boundL) t :|: replaceCoterm (outerR, freeR, boundR) (outerL, freeL, boundL) c
  Let t b -> Let (replaceTerm (outerR, freeR, boundR) (outerL, freeL, boundL) t) (replaceCommand (succ outerR, freeR, boundR) (outerL, freeL, boundL) b)

replace :: (Index -> Name -> Term, Index -> Index -> Term) -> (Index -> Name -> Coterm, Index -> Index -> Coterm) -> (Command -> Command)
replace (freeR, boundR) (freeL, boundL) = replaceCommand (0, freeR, boundR) (0, freeL, boundL)
