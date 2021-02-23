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

import           Control.Effect.NonDet
import           Control.Lens (Lens', coerced, lens)
import           Control.Monad ((<=<))
import           Data.Bifunctor (first)
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


lookupC :: (Alternative m, Monad m) => Name -> Module -> m (ScopeEntry (Q Name))
lookupC n Module{ name, scope } = foldMapA matchDef (decls scope)
  where
  matchDef = fmap (first (name :.:)) . lookupScope n . tm <=< unDData

-- | Look up effect operations.
lookupE :: (Alternative m, Monad m) => Name -> Module -> m (ScopeEntry (Q Name))
lookupE n Module{ name, scope } = foldMapA matchDef (decls scope)
  where
  matchDef = fmap (first (name:.:)) . lookupScope n . tm <=< unDInterface

lookupD :: Alternative m => Name -> Module -> m (ScopeEntry (Q Name))
lookupD n Module{ name, scope } = maybe empty pure $ do
  d <- Map.lookup n (decls scope)
  pure $ name:.:n :=: d


newtype Scope = Scope { decls :: Map.Map Name Def }
  deriving (Monoid, Semigroup)

type ScopeEntry n = n :=: Def

decls_ :: Lens' Scope (Map.Map Name Def)
decls_ = coerced

scopeFromList :: [ScopeEntry Name] -> Scope
scopeFromList = Scope . Map.fromList . map (\ (n :=: d) -> (n, d))

scopeToList :: Scope -> [ScopeEntry Name]
scopeToList = map (uncurry (:=:)) . Map.toList . decls

lookupScope :: Alternative m => Name -> Scope -> m (ScopeEntry Name)
lookupScope n (Scope ds) = maybe empty (pure . (n :=:)) (Map.lookup n ds)


newtype Import = Import { name :: MName }


data Def
  = DTerm (Maybe (Expr P)) (Type P)
  | DData Scope (Type T)
  | DInterface Scope (Type T)
  | DModule Scope (Type T)

unDTerm :: Alternative m => Def -> m (Maybe (Expr P) ::: Type P)
unDTerm = \case
  DTerm e _T -> pure (e ::: _T)
  _          -> empty

unDData :: Alternative m => Def -> m (Scope ::: Type T)
unDData = \case
  DData cs _T -> pure (cs ::: _T)
  _           -> empty

unDInterface :: Alternative m => Def -> m (Scope ::: Type T)
unDInterface = \case
  DInterface cs _T -> pure (cs ::: _T)
  _                -> empty
