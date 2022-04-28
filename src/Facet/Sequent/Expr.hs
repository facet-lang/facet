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
, muR
, lamR
, lamR'
, let'
) where

import Data.Bifunctor (bimap)
import Data.Function ((&))
import Data.Text (Text)
import Data.These
import Facet.Name
import Facet.Snoc
import Facet.Snoc.NonEmpty
import Facet.Syntax
import Fresnel.Lens (Lens', lens)
import Fresnel.Prism
import Fresnel.Setter ((%~))

-- Terms

data Term
  = Var (Var Index)
  | MuR Scope
  | LamR Scope
  | SumR Name Term
  | UnitR
  | PrdR Term Term
  | StringR Text


-- Coterms

data Coterm
  = Covar (Var Index)
  | MuL Scope
  | LamL Term Coterm
  | SumL [Name :=: Coterm]
  | UnitL
  | PrdL1 Coterm
  | PrdL2 Coterm


-- Commands

data Command
  = Term :|: Coterm
  | Let Term Scope


-- Scopes

newtype Scope = Scope { getScope :: Command }

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

outer_ :: Lens' (Replacer t) Index
outer_ = lens outer (\ Replacer{ free, bound } outer -> Replacer{ outer, free, bound })

free' :: Replacer t -> Name -> t
free' Replacer{ outer, free } = free outer

bound' :: Replacer t -> Index -> t
bound' Replacer{ outer, bound } = bound outer

replaceTerm :: These (Replacer Coterm) (Replacer Term) -> (Term -> Term)
replaceTerm lr within = case within of
  Var (Free (Nil:|>n)) -> that (const within) free' lr n
  Var (Free _)         -> within
  Var (Bound inner)    -> that (const within) bound' lr inner
  MuR (Scope b)        -> MuR (Scope (replaceCommand (lr & _This.outer_ %~ succ) b))
  LamR (Scope b)       -> LamR (Scope (replaceCommand (lr & _This.outer_ %~ succ & _That.outer_ %~ succ) b))
  SumR i a             -> SumR i (replaceTerm lr a)
  UnitR                -> within
  PrdR a b             -> PrdR (replaceTerm lr a) (replaceTerm lr b)
  StringR _            -> within
  where
  that :: c -> (b -> c) -> These a b -> c
  that d f = these (const d) f (const f)

replaceCoterm :: These (Replacer Coterm) (Replacer Term) -> (Coterm -> Coterm)
replaceCoterm lr within = case within of
  Covar (Free (Nil:|>n)) -> this (const within) free' lr n
  Covar (Free _)         -> within
  Covar (Bound inner)    -> this (const within) bound' lr inner
  MuL (Scope b)          -> MuL (Scope (replaceCommand (lr & _That.outer_ %~ succ) b))
  LamL a k               -> LamL (replaceTerm lr a) (replaceCoterm lr k)
  SumL cs                -> SumL (map (fmap (replaceCoterm lr)) cs)
  UnitL                  -> within
  PrdL1 k                -> PrdL1 (replaceCoterm lr k)
  PrdL2 k                -> PrdL2 (replaceCoterm lr k)
  where
  this :: c -> (a -> c) -> These a b -> c
  this d f = these f (const d) (const . f)

replaceCommand :: These (Replacer Coterm) (Replacer Term) -> (Command -> Command)
replaceCommand lr = \case
  t :|: c         -> replaceTerm lr t :|: replaceCoterm lr c
  Let t (Scope b) -> Let (replaceTerm lr t) (Scope (replaceCommand (lr & _That.outer_ %~ succ) b))


_This :: Prism' (These a b) a
_This = prism' This (these Just (const Nothing) (const (const Nothing)))

_That :: Prism' (These a b) b
_That = prism' That (these (const Nothing) Just (const (const Nothing)))


-- Smart constructors

muR :: Name -> Command -> Term
muR name body = MuR (abstractLR (This name) body)

lamR :: Name -> Name -> Command -> Term
lamR v k body = LamR (abstractLR (These v k) body)

lamR' :: Name -> Name -> Term -> Term
lamR' var covar body = lamR var covar (body :|: Covar (Free (q covar)))


let' :: Name -> Term -> Command -> Command
let' name value body = Let value (abstractLR (That name) body)
