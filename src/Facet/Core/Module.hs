module Facet.Core.Module
( -- * Modules
  Module(..)
, name_
, imports_
, scope_
, lookupC
, lookupE
, lookupD
, Scope(..)
, ScopeEntry
, decls_
, scopeFromList
, scopeToList
, lookupScope
, Import(..)
, Def(..)
, unDTerm
, unDData
, unDInterface
) where

import           Control.Applicative (Alternative(..))
import           Control.Lens (Lens', coerced, lens)
import           Data.Foldable (asum)
import qualified Data.Map as Map
import           Facet.Core.Term
import           Facet.Core.Type
import           Facet.Name
import           Facet.Syntax

-- Modules

-- FIXME: model operators and their associativities for parsing.
data Module = Module
  { name      :: MName
  -- FIXME: record source references to imports to contextualize ambiguous name errors.
  , imports   :: [Import]
  -- FIXME: record source references to operators to contextualize parse errors.
  , operators :: [(Op, Assoc)]
  -- FIXME: record source references to definitions to contextualize ambiguous name errors.
  , scope     :: Scope
  }

name_ :: Lens' Module MName
name_ = lens (\ Module{ name } -> name) (\ m name -> (m :: Module){ name })

imports_ :: Lens' Module [Import]
imports_ = lens imports (\ m imports -> m{ imports })

scope_ :: Lens' Module Scope
scope_ = lens scope (\ m scope -> m{ scope })


lookupC :: Alternative m => Name -> Module -> m (Q Name :=: Maybe (Def P) ::: Type P)
lookupC n Module{ name, scope } = maybe empty pure $ asum (matchDef <$> decls scope)
  where
  matchDef (d ::: _) = do
    n :=: v ::: _T <- maybe empty pure d >>= unDData >>= lookupScope n
    pure $ name:.:n :=: v ::: _T

-- | Look up effect operations.
lookupE :: Alternative m => Name -> Module -> m (Q Name :=: Maybe (Def P) ::: Type P)
lookupE n Module{ name, scope } = maybe empty pure $ asum (matchDef <$> decls scope)
  where
  matchDef (d ::: _) = do
    n :=: _ ::: _T <- maybe empty pure d >>= unDInterface >>= lookupScope n
    pure $ name:.:n :=: Nothing ::: _T

lookupD :: Alternative m => Name -> Module -> m (Q Name :=: Maybe (Def P) ::: Type P)
lookupD n Module{ name, scope } = maybe empty pure $ do
  d ::: _T <- Map.lookup n (decls scope)
  pure $ name:.:n :=: d ::: _T


newtype Scope = Scope { decls :: Map.Map Name (Maybe (Def P) ::: Type P) }
  deriving (Monoid, Semigroup)

type ScopeEntry = Name :=: Maybe (Def P) ::: Type P

decls_ :: Lens' Scope (Map.Map Name (Maybe (Def P) ::: Type P))
decls_ = coerced

scopeFromList :: [ScopeEntry] -> Scope
scopeFromList = Scope . Map.fromList . map (\ (n :=: v ::: _T) -> (n, v ::: _T))

scopeToList :: Scope -> [ScopeEntry]
scopeToList = map (\ (n, v ::: _T) -> n :=: v ::: _T) . Map.toList . decls

lookupScope :: Alternative m => Name -> Scope -> m ScopeEntry
lookupScope n (Scope ds) = maybe empty (pure . (n :=:)) (Map.lookup n ds)


newtype Import = Import { name :: MName }


data Def u
  = DTerm (Expr P)
  | DData Scope
  | DInterface Scope
  | DModule Scope

unDTerm :: Alternative m => Def P -> m (Expr P)
unDTerm = \case
  DTerm expr -> pure expr
  _          -> empty

unDData :: Alternative m => Def T -> m Scope
unDData = \case
  DData cs -> pure cs
  _        -> empty

unDInterface :: Alternative m => Def T -> m Scope
unDInterface = \case
  DInterface cs -> pure cs
  _             -> empty
