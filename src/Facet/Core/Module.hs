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

import           Control.Applicative (Alternative(..))
import           Control.Lens (Lens', coerced, lens)
import           Control.Monad ((<=<))
import           Data.Bifunctor (first)
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


lookupC :: Alternative m => Name -> Module -> m (RName :=: Maybe Expr ::: Type)
lookupC n Module{ name, scope } = maybe empty pure $ asum (matchDef <$> decls scope)
  where
  matchDef = matchTerm <=< lookupScope n . tm <=< unDData
  matchTerm (n :=: d) = (name :.: n :=:) <$> unDTerm d

-- | Look up effect operations.
lookupE :: Alternative m => Name -> Module -> m (RName :=: Def)
lookupE n Module{ name, scope } = maybe empty pure $ asum (matchDef <$> decls scope)
  where
  matchDef = fmap (first (name:.:)) . lookupScope n . tm <=< unDInterface

lookupD :: Alternative m => Name -> Module -> m (RName :=: Def)
lookupD n Module{ name, scope } = maybe empty (pure . first (name:.:)) (lookupScope n scope)


newtype Scope = Scope { decls :: Map.Map Name Def }
  deriving (Monoid, Semigroup)

decls_ :: Lens' Scope (Map.Map Name Def)
decls_ = coerced

scopeFromList :: [Name :=: Def] -> Scope
scopeFromList = Scope . Map.fromList . map (\ (n :=: v) -> (n, v))

scopeToList :: Scope -> [Name :=: Def]
scopeToList = map (uncurry (:=:)) . Map.toList . decls

lookupScope :: Alternative m => Name -> Scope -> m (Name :=: Def)
lookupScope n (Scope ds) = maybe empty (pure . (n :=:)) (Map.lookup n ds)


newtype Import = Import { name :: MName }


data Def
  = DTerm (Maybe Expr) Type
  | DData Scope Type
  | DInterface Scope Type
  | DModule Scope Type

unDTerm :: Alternative m => Def -> m (Maybe Expr ::: Type)
unDTerm = \case
  DTerm expr _T -> pure $ expr ::: _T
  _             -> empty

unDData :: Alternative m => Def -> m (Scope ::: Type)
unDData = \case
  DData cs _K -> pure $ cs ::: _K
  _           -> empty

unDInterface :: Alternative m => Def -> m (Scope ::: Type)
unDInterface = \case
  DInterface cs _K -> pure $ cs ::: _K
  _                -> empty
