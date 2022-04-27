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
) where

import Data.Function ((&))
import Data.Text (Text)
import Facet.Name
import Facet.Snoc
import Facet.Snoc.NonEmpty
import Facet.Syntax
import Fresnel.Lens (Lens', lens)
import Fresnel.Maybe
import Fresnel.Setter ((%~))

-- Terms

data Term
  = Var (Var Index)
  | MuR Scope
  | LamR Scope
  | SumR Int Term
  | BottomR Scope
  | UnitR
  | PrdR Term Term
  | StringR Text


-- Coterms

data Coterm
  = Covar (Var Index)
  | MuL Scope
  | LamL Term Coterm
  | SumL [Coterm]
  | UnitL
  | PrdL1 Coterm
  | PrdL2 Coterm


-- Commands

data Command
  = Term :|: Coterm
  | Let Term Scope


-- Scopes

newtype Scope = Scope { getScope :: Command }

abstractL, abstractR :: Maybe Name -> (Command -> Scope)
abstractL c = abstractLR c Nothing
abstractR t = abstractLR Nothing t

abstractLR :: Maybe Name -> Maybe Name -> (Command -> Scope)
abstractLR Nothing Nothing = Scope
abstractLR c t = Scope . replaceCommand (Replacer 0 . freeL <$> c <*> pure boundL) (Replacer 0 . freeR <$> t <*> pure boundR) where
  freeR t outer name
    | name == t = Var (Bound outer)
    | otherwise = Var (Free (q name))
  freeL c outer name
    | name == c = Covar (Bound outer)
    | otherwise = Covar (Free (q name))
  boundR _ inner = Var (Bound inner)
  boundL _ inner = Covar (Bound inner)

instantiateL :: Maybe Coterm ->  (Scope -> Command)
instantiateL c = instantiateLR c Nothing

instantiateR :: Maybe Term   -> (Scope -> Command)
instantiateR t = instantiateLR Nothing t

instantiateLR :: Maybe Coterm -> Maybe Term -> (Scope -> Command)
instantiateLR Nothing Nothing = getScope
instantiateLR c t = replaceCommand (Replacer 0 freeL . boundL <$> c) (Replacer 0 freeR . boundR <$> t) . getScope where
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

replaceTerm :: Maybe (Replacer Coterm) -> Maybe (Replacer Term) -> (Term -> Term)
replaceTerm l r within = case within of
  Var (Free (Nil:|>n)) -> maybe (const within) free' r n
  Var (Free _)         -> within
  Var (Bound inner)    -> maybe (const within) bound' r inner
  MuR (Scope b)        -> MuR (Scope (replaceCommand (l & _Just.outer_ %~ succ) r b))
  LamR (Scope b)       -> LamR (Scope (replaceCommand (l & _Just.outer_ %~ succ) (r & _Just.outer_ %~ succ) b))
  SumR i a             -> SumR i (replaceTerm l r a)
  BottomR (Scope b)    -> BottomR (Scope (replaceCommand l r b))
  UnitR                -> within
  PrdR a b             -> PrdR (replaceTerm l r a) (replaceTerm l r b)
  StringR _            -> within

replaceCoterm :: Maybe (Replacer Coterm) -> Maybe (Replacer Term) -> (Coterm -> Coterm)
replaceCoterm l r within = case within of
  Covar (Free (Nil:|>n)) -> maybe (const within) free' l n
  Covar (Free _)         -> within
  Covar (Bound inner)    -> maybe (const within) bound' l inner
  MuL (Scope b)          -> MuL (Scope (replaceCommand l (r & _Just.outer_ %~ succ) b))
  LamL a k               -> LamL (replaceTerm l r a) (replaceCoterm l r k)
  SumL cs                -> SumL (map (replaceCoterm l r) cs)
  UnitL                  -> within
  PrdL1 k                -> PrdL1 (replaceCoterm l r k)
  PrdL2 k                -> PrdL2 (replaceCoterm l r k)

replaceCommand :: Maybe (Replacer Coterm) -> Maybe (Replacer Term) -> (Command -> Command)
replaceCommand l r = \case
  t :|: c         -> replaceTerm l r t :|: replaceCoterm l r c
  Let t (Scope b) -> Let (replaceTerm l r t) (Scope (replaceCommand l (r & _Just.outer_ %~ succ) b))


-- Smart constructors

muR :: Name -> Command -> Term
muR name body = MuR (abstractLR (Just name) Nothing body)

lamR :: Name -> Name -> Command -> Term
lamR v k body = LamR (abstractLR (Just v) (Just k) body)
