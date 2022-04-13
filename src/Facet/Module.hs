module Facet.Module
( -- * Modules
  Module(..)
, name_
, imports_
, scope_
, foldMapC
, lookupC
, lookupE
, lookupD
, Scope(..)
, decls_
, toList_
, scopeFromList
, scopeToList
, lookupScope
, Import(..)
, Submodule(..)
, _SData
, _SInterface
, _SModule
, Def(..)
, _DSubmodule
, _DData
, _DInterface
, _DModule
) where

import           Control.Algebra
import           Control.Effect.Choose
import           Control.Effect.Empty
import           Control.Monad ((<=<))
import           Data.Bifunctor (Bifunctor(bimap), first)
import           Data.Bitraversable
import           Data.Coerce
import qualified Data.Map as Map
import           Facet.Kind
import           Facet.Name
import           Facet.Snoc.NonEmpty ((|>))
import           Facet.Syntax
import           Facet.Term.Expr
import           Facet.Type.Norm
import           Fresnel.Fold (preview)
import           Fresnel.Getter (view)
import           Fresnel.Iso (Iso, coerced, fmapping, iso)
import           Fresnel.Lens (Lens', lens)
import           Fresnel.Prism
import           Fresnel.Review (review)

-- Modules

-- FIXME: model operators and their associativities for parsing.
data Module = Module
  { name      :: QName
  -- FIXME: record source references to imports to contextualize ambiguous name errors.
  , imports   :: [Import]
  -- FIXME: record source references to operators to contextualize parse errors.
  , operators :: [(Op, Assoc)]
  -- FIXME: record source references to definitions to contextualize ambiguous name errors.
  , scope     :: Scope Def
  }

name_ :: Lens' Module QName
name_ = lens (\ Module{ name } -> name) (\ Module{ imports, operators, scope } name -> Module{ name, imports, operators, scope })

imports_ :: Lens' Module [Import]
imports_ = lens imports (\ m imports -> m{ imports })

scope_ :: Lens' Module (Scope Def)
scope_ = lens scope (\ m scope -> m{ scope })


foldMapC :: (Foldable t, Has (Choose :+: Empty) sig m) => (a -> m b) -> t a -> m b
foldMapC f = getChoosing #. foldMap (Choosing #. f)
{-# INLINE foldMapC #-}


-- | Compose a function operationally equivalent to 'id' on the left.
--
--   cf https://github.com/fused-effects/diffused-effects/pull/1#discussion_r323560758
(#.) :: Coercible b c => (b -> c) -> (a -> b) -> (a -> c)
(#.) _ = coerce
{-# INLINE (#.) #-}


lookupC :: Has (Choose :+: Empty) sig m => Name -> Module -> m (QName :=: Maybe Term ::: Type)
lookupC n Module{ name, scope } = foldMapC matchDef (map (view def_) (decls scope))
  where
  matchDef = matchTerm <=< lookupScope n . view tm_ <=< maybe empty pure . preview _DData
  matchTerm (n :=: d) = (name |> n :=:) <$> maybe empty pure (preview _DTerm d)

-- | Look up effect operations.
lookupE :: Has (Choose :+: Empty) sig m => Name -> Module -> m (QName :=: Def)
lookupE n Module{ name, scope } = foldMapC matchDef (map (view def_) (decls scope))
  where
  matchDef = fmap (bimap (name |>) (DTerm Nothing)) . lookupScope n . view tm_ <=< maybe empty pure . preview _DInterface

lookupD :: Has Empty sig m => Name -> Module -> m (QName :=: Def)
lookupD n Module{ name, scope } = maybe empty (pure . first (name |>)) (lookupScope n scope)


newtype Scope a = Scope { decls :: [Name :=: a] }
  deriving (Monoid, Semigroup)

decls_ :: Iso (Scope a) (Scope b) (Map.Map Name a) (Map.Map Name b)
decls_ = toList_.fmapping pair_.iso Map.fromList Map.toList

toList_ :: Iso (Scope a) (Scope b) [Name :=: a] [Name :=: b]
toList_ = coerced

scopeFromList :: [Name :=: a] -> Scope a
scopeFromList = review toList_

scopeToList :: Scope a -> [Name :=: a]
scopeToList = view toList_

lookupScope :: Has Empty sig m => Name -> Scope a -> m (Name :=: a)
lookupScope n (Scope ds) = maybe empty (pure . (n :=:)) (lookup n (map (\ (n :=: a) -> (n, a)) ds))


newtype Import = Import { name :: QName }


data Submodule
  = SData (Scope Def)
  | SInterface (Scope Type)
  | SModule (Scope Def)

_SData :: Prism' Submodule (Scope Def)
_SData = prism' SData (\case
  SData cs -> Just cs
  _        -> Nothing)

_SInterface :: Prism' Submodule (Scope Type)
_SInterface = prism' SInterface (\case
  SInterface os -> Just os
  _             -> Nothing)

_SModule :: Prism' Submodule (Scope Def)
_SModule = prism' SModule (\case
  SModule ds -> Just ds
  _          -> Nothing)


data Def
  = DTerm (Maybe Term) Type
  | DSubmodule Submodule Kind

_DTerm :: Prism' Def (Maybe Term ::: Type)
_DTerm = prism' (\ (t ::: _T) -> DTerm t _T) (\case
  DTerm t _T -> Just (t ::: _T)
  _          -> Nothing)

_DSubmodule :: Prism' Def (Submodule ::: Kind)
_DSubmodule = prism' (\ (s ::: _K) -> DSubmodule s _K) (\case
  DSubmodule s _K -> Just (s ::: _K)
  _               -> Nothing)

_DData :: Prism' Def (Scope Def ::: Kind)
_DData = onFst _DSubmodule _SData

_DInterface :: Prism' Def (Scope Type ::: Kind)
_DInterface = onFst _DSubmodule _SInterface

_DModule :: Prism' Def (Scope Def ::: Kind)
_DModule = onFst _DSubmodule _SModule

onFst :: Bitraversable f => Prism' s (f a c) -> Prism' a b -> Prism' s (f b c)
onFst p q = prism' (review p . first (review q)) (bitraverse (preview q) pure <=< preview p)
