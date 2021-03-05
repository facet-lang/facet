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


lookupC :: (Alternative m, Monad m) => Name -> Module -> m (QName :=: Maybe PExpr ::: Pos Type)
lookupC n Module{ name, scope } = foldMapA matchDef (decls scope)
  where
  matchDef = matchTerm <=< lookupScope n . tm <=< unDData
  matchTerm (n :=: d) = (name :.: n :=: ) <$> unDTerm d

-- | Look up effect operations.
lookupE :: (Alternative m, Monad m) => Name -> Module -> m (QName :=: Def)
lookupE n Module{ name, scope } = foldMapA matchDef (decls scope)
  where
  matchDef = fmap (first (name:.:)) . lookupScope n . tm <=< unDInterface

lookupD :: Alternative m => Name -> Module -> m (QName :=: Def)
lookupD n Module{ name, scope } = maybe empty (pure . first (name:.:)) (lookupScope n scope)


newtype Scope = Scope { decls :: Map.Map Name Def }
  deriving (Monoid, Semigroup)

decls_ :: Lens' Scope (Map.Map Name Def)
decls_ = coerced

scopeFromList :: [Name :=: Def] -> Scope
scopeFromList = Scope . Map.fromList . map (\ (n :=: d) -> (n, d))

scopeToList :: Scope -> [Name :=: Def]
scopeToList = map (uncurry (:=:)) . Map.toList . decls

lookupScope :: Alternative m => Name -> Scope -> m (Name :=: Def)
lookupScope n (Scope ds) = maybe empty (pure . (n :=:)) (Map.lookup n ds)


newtype Import = Import { name :: MName }


data Def
  = DTerm (Maybe PExpr) (Pos Type)
  | DData Scope Kind
  | DInterface Scope Kind
  | DModule Scope Kind

unDTerm :: Alternative m => Def -> m (Maybe PExpr ::: Pos Type)
unDTerm = \case
  DTerm e _T -> pure (e ::: _T)
  _          -> empty

unDData :: Alternative m => Def -> m (Scope ::: Kind)
unDData = \case
  DData cs _T -> pure (cs ::: _T)
  _           -> empty

unDInterface :: Alternative m => Def -> m (Scope ::: Kind)
unDInterface = \case
  DInterface cs _T -> pure (cs ::: _T)
  _                -> empty
