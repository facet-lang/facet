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

replaceTerm :: Index -> Index -> (Index -> Name -> Term) -> (Index -> Index -> Term) -> (Index -> Name -> Coterm) -> (Index -> Index -> Coterm) -> (Term -> Term)
replaceTerm outerL outerR freeR boundR freeL boundL within = case within of
  Var (Free (Nil:|>n)) -> freeR outerR n
  Var (Free _)         -> within
  Var (Bound inner)    -> boundR outerR inner
  MuR b                -> MuR (replaceCommand (succ outerL) outerR freeR boundR freeL boundL b)
  LamR b               -> LamR (replaceCommand (succ outerL) (succ outerR) freeR boundR freeL boundL b)
  SumR i a             -> SumR i (replaceTerm outerL outerR freeR boundR freeL boundL a)
  BottomR b            -> BottomR (replaceCommand outerL outerR freeR boundR freeL boundL b)
  UnitR                -> within
  PrdR a b             -> PrdR (replaceTerm outerL outerR freeR boundR freeL boundL a) (replaceTerm outerL outerR freeR boundR freeL boundL b)
  StringR _            -> within

replaceCoterm :: Index -> Index -> (Index -> Name -> Term) -> (Index -> Index -> Term) -> (Index -> Name -> Coterm) -> (Index -> Index -> Coterm) -> (Coterm -> Coterm)
replaceCoterm outerL outerR freeR boundR freeL boundL within = case within of
  Covar (Free (Nil:|>n)) -> freeL outerL n
  Covar (Free _)         -> within
  Covar (Bound inner)    -> boundL outerL inner
  MuL b                  -> MuL (replaceCommand outerL (succ outerR) freeR boundR freeL boundL b)
  LamL a k               -> LamL (replaceTerm outerL outerR freeR boundR freeL boundL a) (replaceCoterm outerL outerR freeR boundR freeL boundL k)
  SumL cs                -> SumL (map (replaceCoterm outerL outerR freeR boundR freeL boundL) cs)
  UnitL                  -> within
  PrdL1 k                -> PrdL1 (replaceCoterm outerL outerR freeR boundR freeL boundL k)
  PrdL2 k                -> PrdL2 (replaceCoterm outerL outerR freeR boundR freeL boundL k)

replaceCommand :: Index -> Index -> (Index -> Name -> Term) -> (Index -> Index -> Term) -> (Index -> Name -> Coterm) -> (Index -> Index -> Coterm) -> (Command -> Command)
replaceCommand outerL outerR freeR boundR freeL boundL = \case
  t :|: c -> replaceTerm outerL outerR freeR boundR freeL boundL t :|: replaceCoterm outerL outerR freeR boundR freeL boundL c
  Let t b -> Let (replaceTerm outerL outerR freeR boundR freeL boundL t) (replaceCommand outerL (succ outerR) freeR boundR freeL boundL b)

replace :: (Index -> Name -> Term, Index -> Index -> Term) -> (Index -> Name -> Coterm, Index -> Index -> Coterm) -> (Command -> Command)
replace (freeR, boundR) (freeL, boundL) = replaceCommand 0 0 freeR boundR freeL boundL
