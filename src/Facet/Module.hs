{-# LANGUAGE TypeFamilies #-}
module Facet.Module
( -- * Modules
  Module(..)
, name_
, imports_
, scope_
, foldMapC
, lookupConstructor
, lookupOperation
, lookupDef
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

import Control.Algebra
import Control.Effect.Choose
import Control.Effect.Empty
import Data.Coerce
import Facet.Kind
import Facet.Name
import Facet.Scope
import Facet.Syntax
import Facet.Term.Expr
import Facet.Type.Norm
import Fresnel.Fold (folded, preview, (^?))
import Fresnel.Ixed
import Fresnel.Lens (Lens', lens)
import Fresnel.Optional (Optional')
import Fresnel.Prism

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


lookupConstructor :: Has (Choose :+: Empty) sig m => Name -> Module -> m (QName :=: Type)
lookupConstructor n Module{ name, scope } = maybe empty (pure . (name // n :=:)) (scope ^? toList_.folded.def_._DData.ix n)

-- | Look up effect operations.
lookupOperation :: Has (Choose :+: Empty) sig m => Name -> Module -> m (QName :=: Type)
lookupOperation n Module{ name, scope } = maybe empty (pure . (name // n :=:)) (scope ^? toList_.folded.def_._DInterface.ix n)

lookupDef :: Has Empty sig m => Name -> Module -> m Def
lookupDef n = maybe empty pure . preview (scope_.ix n)


newtype Import = Import { name :: QName }


data Submodule
  = SData (Scope Type)
  | SInterface (Scope Type)
  | SModule (Scope Def)

_SData :: Prism' Submodule (Scope Type)
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

_DData :: Optional' Def (Scope Type)
_DData = _DSubmodule.tm_._SData

_DInterface :: Optional' Def (Scope Type)
_DInterface = _DSubmodule.tm_._SInterface

_DModule :: Optional' Def (Scope Def)
_DModule = _DSubmodule.tm_._SModule
