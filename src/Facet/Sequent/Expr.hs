module Facet.Sequent.Expr
( -- * Terms
  Term(..)
  -- * Coterms
, Coterm(..)
  -- * Commands
, Command(..)
  -- * Scopes
, Scope
, abstractL
, abstractR
, abstractLR
, instantiateL
, instantiateR
, instantiateLR
  -- * Smart constructors
, freeR
, globalR
, boundR
, muR
, lamR
, lamR'
, freeL
, boundL
, muL
, let'
) where

import Data.Bifunctor (Bifunctor(..))
import Data.String
import Data.Text (Text)
import Data.These
import Facet.Name
import Facet.Snoc
import Facet.Snoc.NonEmpty
import Facet.Syntax

-- Terms

data Term
  = Var (Var Index)
  | MuR Scope
  | LamR Scope
  | SumR Name Term
  | PrdR [Term]
  | StringR Text
  deriving (Show)

instance IsString Term where
  fromString = freeR . fromString


-- Coterms

data Coterm
  = Covar (Var Index)
  | MuL Scope
  | LamL Term Coterm
  | SumL [Name :=: Coterm]
  | PrdL Int Coterm
  deriving (Show)

instance IsString Coterm where
  fromString = freeL . fromString


-- Commands

data Command
  = Term :|: Coterm
  | Let Term Scope
  deriving (Show)

infix 2 :|:


-- Scopes

newtype Scope = Scope { getScope :: Command }
  deriving (Show)

abstractL, abstractR :: Name -> (Command -> Scope)
abstractL c = abstractLR (This c)
abstractR t = abstractLR (That t)

abstractLR :: These Name Name -> (Command -> Scope)
abstractLR ct = Scope . replaceCommand (bimap (\ c -> Replacer 0 (freeL c) boundL) (\ t -> Replacer 0 (freeR t) boundR) ct) where
  freeR t outer name
    | name == t = Var (Bound outer)
    | otherwise = Var (Free (q name))
  freeL c outer name
    | name == c = Covar (Bound outer)
    | otherwise = Covar (Free (q name))
  boundR _ inner = Var (Bound inner)
  boundL _ inner = Covar (Bound inner)

instantiateL :: Coterm ->  (Scope -> Command)
instantiateL c = instantiateLR (This c)

instantiateR :: Term   -> (Scope -> Command)
instantiateR t = instantiateLR (That t)

instantiateLR :: These Coterm Term -> (Scope -> Command)
instantiateLR ct = replaceCommand (bimap (Replacer 0 freeL . boundL) (Replacer 0 freeR . boundR) ct) . getScope where
  freeR _ name = Var   (Free (q name))
  freeL _ name = Covar (Free (q name))
  boundR t outer inner
    | outer == inner = t
    | otherwise      = Var (Bound inner)
  boundL c outer inner
    | outer == inner = c
    | otherwise      = Covar (Bound inner)

data Replacer t = Replacer
  { outer :: Index
  , free  :: Index -> Name -> t
  , bound :: Index -> Index -> t
  }

free' :: Replacer t -> Name -> t
free' Replacer{ outer, free } = free outer

bound' :: Replacer t -> Index -> t
bound' Replacer{ outer, bound } = bound outer

incr :: Replacer t -> Replacer t
incr r@Replacer{ outer } = r{ outer = outer + 1}


replaceTerm :: These (Replacer Coterm) (Replacer Term) -> (Term -> Term)
replaceTerm lr within = case within of
  Var (Free (Nil:|>n)) -> that (const within) free' lr n
  Var (Free _)         -> within
  Var (Bound inner)    -> that (const within) bound' lr inner
  MuR (Scope b)        -> MuR (Scope (replaceCommand (first incr lr) b))
  LamR (Scope b)       -> LamR (Scope (replaceCommand (bimap incr incr lr) b))
  SumR i a             -> SumR i (replaceTerm lr a)
  PrdR as              -> PrdR (map (replaceTerm lr) as)
  StringR _            -> within
  where
  that :: c -> (b -> c) -> These a b -> c
  that d f = these (const d) f (const f)

replaceCoterm :: These (Replacer Coterm) (Replacer Term) -> (Coterm -> Coterm)
replaceCoterm lr within = case within of
  Covar (Free (Nil:|>n)) -> this (const within) free' lr n
  Covar (Free _)         -> within
  Covar (Bound inner)    -> this (const within) bound' lr inner
  MuL (Scope b)          -> MuL (Scope (replaceCommand (second incr lr) b))
  LamL a k               -> LamL (replaceTerm lr a) (replaceCoterm lr k)
  SumL cs                -> SumL (map (fmap (replaceCoterm lr)) cs)
  PrdL i b               -> PrdL i (replaceCoterm lr b)
  where
  this :: c -> (a -> c) -> These a b -> c
  this d f = these f (const d) (const . f)

replaceCommand :: These (Replacer Coterm) (Replacer Term) -> (Command -> Command)
replaceCommand lr = \case
  t :|: c         -> replaceTerm lr t :|: replaceCoterm lr c
  Let t (Scope b) -> Let (replaceTerm lr t) (Scope (replaceCommand (second incr lr) b))


-- Smart constructors

freeR :: Name -> Term
freeR = Var . Free . q

globalR :: QName -> Term
globalR = Var . Free

boundR :: Index -> Term
boundR = Var . Bound

muR :: Name -> Command -> Term
muR name body = MuR (abstractLR (This name) body)

lamR :: Name -> Name -> Command -> Term
lamR k v body = LamR (abstractLR (These k v) body)

lamR' :: Name -> Term -> Term
lamR' name body = lamR name name (body :|: Covar (Free (q name)))


freeL :: Name -> Coterm
freeL = Covar . Free . q

boundL :: Index -> Coterm
boundL = Covar . Bound

muL :: Name -> Command -> Coterm
muL name body = MuL (abstractLR (That name) body)


let' :: Name -> Term -> Command -> Command
let' name value body = Let value (abstractLR (That name) body)
