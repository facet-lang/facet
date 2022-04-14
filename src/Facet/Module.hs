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
, Scope(..)
, decls_
, toList_
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
import           Fresnel.Ixed
import           Fresnel.Lens (Lens', lens)
import           Fresnel.Optional (Optional', optional')
import           Fresnel.Prism

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
lookupConstructor n Module{ name, scope } = foldMapC matchDef (map (view def_) (decls scope))
  where
  matchDef = maybe empty (pure . (name |> n :=:)) . preview (_DData.ix n)

-- | Look up effect operations.
lookupOperation :: Has (Choose :+: Empty) sig m => Name -> Module -> m (QName :=: Def)
lookupOperation n Module{ name, scope } = foldMapC matchDef (map (view def_) (decls scope))
  where
  matchDef = maybe empty (pure . ((name |> n :=:) . DTerm Nothing)) . preview (_DInterface.ix n)

lookupDef :: Has Empty sig m => Name -> Module -> m (QName :=: Def)
lookupDef n Module{ name, scope } = maybe empty (pure . (name |> n :=:)) (preview (ix n) scope)


newtype Scope a = Scope { decls :: [Name :=: a] }
  deriving (Functor, Monoid, Semigroup)

instance Ixed (Scope a) where
  type Index (Scope a) = Name
  type IxValue (Scope a) = a
  ix n = optional' prj (\ (Scope ds) d' -> Scope (replace (\ (n' :=: _) -> (n' :=: d') <$ guard (n == n')) ds))
    where
    prj = maybe empty pure . lookup n . map (\ (n :=: a) -> (n, a)) . decls
    replace _ []     = []
    replace f (v:vs) = case f v of
      Nothing -> v:replace f vs
      Just v' -> v':vs

decls_ :: Iso (Scope a) (Scope b) (Map.Map Name a) (Map.Map Name b)
decls_ = toList_.fmapping pair_.iso Map.fromList Map.toList

toList_ :: Iso (Scope a) (Scope b) [Name :=: a] [Name :=: b]
toList_ = coerced


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
